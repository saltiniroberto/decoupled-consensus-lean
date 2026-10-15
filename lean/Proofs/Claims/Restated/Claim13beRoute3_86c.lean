import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_46
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
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86c

/-!
# The FG root against the SG blocks and the previous heads after the deadline

After the progress deadline, a reader's FG root is on one chain with every honest SG block and an
ancestor of every honest head of a later slot, and a run block that is an ancestor of an honest SG
block or head is in the reader's filtered or candidate tree or an ancestor of its FG root. Stated
over a model `M : Record.Model V` along a path `W` of the run.
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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The round-`r` action read computed from `before` can give some node state. -/
private theorem actionReadFrom_nonempty₈₆cn (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` with `lo ≤ opening (a.round − η_SG)` and its awake condition, every round
    `c` at or after the source round with `S.a c` in the horizon has every member of the set for
    `S.a c` that emits along `W` its round-`c` action attestation with every SG block its round-`c`
    action read along `W` can select compatible with the checkpoint `T`. -/
theorem NamedHeightRegimeRunOn.sgHistory_run_l86c (facts : Record.Facts M)
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

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` with the `lo` bound and its awake condition, a read at or after
    `S.a a.round` in the horizon and a reader `u` in the set for the read: if a body of `u`'s store
    in the world of `W` strictly before the read has the store's FG root as justified block and
    justified height at most `blocked`, then that FG root is an ancestor of the checkpoint `T`. -/
theorem NamedHeightRegimeRunOn.fgRoot_preceq_checkpoint_of_low_l86c (facts : Record.Facts M)
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
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read)
    (hhor : read ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    {C : NamedBlock V} (hC : C ∈ (W (strictEventIndex rho read) u).st.bodies)
    (hJ : (M.derive_named S.E S.cfg C).J =
      M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG)
    (hsmall : (M.derive_named S.E S.cfg C).h_j ≤ blocked) :
    Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) T.erase := by
  have hRT := Restated.NamedHeightRegimeRunOn.fgRoot_compatible_after_source_run_l86b
    facts hf hHs hHsXb hX hXXb hcom hbelow h hread hhor hu hlo hA
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
      Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb h
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

/-- Under the bundle with path `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`: if `gstLagged ≤ Γ_neg1 r0`, a
    run-scoped named base holds along `W` at `blocked` whose first crossing is by the inclusive
    index of `S.a deadline`, `deadline ≤ c`, `S.a c` is in the horizon, `read` is from
    `S.a deadline` to `S.a (c + 1)` within the horizon, `u` is in the set for `read`, `v` is in the
    set for `S.a c` and awake for round `c`, and the `lo` bounds hold, then the FG root of `u`'s
    store in the world of `W` strictly before `read` is on one chain with every SG block `v`'s
    round-`c` action read along `W` can select. -/
theorem NamedHeightRegimeBaseRunOn.fgRoot_compatible_actionSGBlock_at_read_after_deadline_l86c
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
    (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c))
    (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
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
      have hRTpre := Restated.NamedHeightRegimeRunOn.fgRoot_preceq_checkpoint_of_low_l86c
        facts hf hHs hHsXb hX hXXb hcom hbelow hreg
        (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone ha).trans
          hread) hreadHor hu hlo hA hC hJ hsmall
      have hloc : lo ≤ Restated.Vocabulary.Execution.Setup.a M S c :=
        (Restated.loBounds_l70 facts S (hreg.seed.round_pos_l70 facts hf) hlo).2.2.2.trans
          (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hac)
      have hSG : G.compatible T.erase = true :=
        Restated.NamedHeightRegimeRunOn.sgHistory_run_l86c facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg hac hhor hlo hA v hv n hn D hD
          (Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf c hv hhor hloc
            hAv (fun j hj => hf.tick_outcome j _ _ hj) n hn D hD) A2 hA2 G hG
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
      obtain ⟨nb, hnb⟩ := actionReadFrom_nonempty₈₆cn facts S
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
        Restated.NamedHeightRegimeRunOn.sgHistory_run_l86c facts hf hHs hHsXb hX
          hXXb hcom hbelow hreg hac hhor hlo hA v hv n hn D hD
          (Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf c hv hhor hloc
            hAv (fun j hj => hf.tick_outcome j _ _ hj) n hn D hD) A2 hA2 G hG
      rw [← hTR]
      exact compatible_of_cases (compatible_cases hSG).symm

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority, the
    weight bound, the recurrence of carrier rounds and the timeout delay bound, and
    `t_GST ≤ S.a rGST`: for a round `c` at or after the progress deadline from `rGST` with `S.a c`
    in the horizon, a read from the deadline's action instant to `S.a (c + 1)` within the horizon,
    `u` in the set for the read, `v` in the set for `S.a c` and awake for round `c`, and the `lo`
    bounds, the FG root of `u`'s store in the world of `W` strictly before the read is on one chain
    with every SG block `v`'s round-`c` action read along `W` can select. -/
theorem fgRoot_compatible_actionSGBlock_at_read_after_GSTOn_l86c (facts : Record.Facts M)
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
    (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
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
  exact Restated.NamedHeightRegimeBaseRunOn.fgRoot_compatible_actionSGBlock_at_read_after_deadline_l86c
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hc hhor hread hreadHor hnext hu hv hAv
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

/-- Under the premises of `fgRoot_preceq_previousHead_through_confirmation_after_GSTOn`, with the
    read at or before `vote_time (s + 1)` in place of `confirmation_time s`: the FG root of `u`'s
    store in the world of `W` strictly before `read` is an ancestor of every head that every member
    of the set for `vote_time s` can vote at `s`. -/
theorem fgRoot_preceq_previousHead_after_GSTOn (facts : Record.Facts M)
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
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot}
    (hs : (M.opening_slot S.hc)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ M.vote_time S.E (s + 1))
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) H := by
  have hbound : M.vote_time S.E (s + 1) ≤ M.confirmation_time S.E s :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)
  exact Restated.fgRoot_preceq_previousHead_through_confirmation_after_GSTOn
    facts S Hs Xb hf hHs hHsXb hcom
    hbelow hrec hdelay hpost hread hhor hs (hnext.trans hbound) hshor hu hloPost hloOpen ht₀ hA

end

/-! ## The filtered tree or the FG root, against an SG block -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_62.lean`, by name. -/
local macro "p62% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_62)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_63.lean`, by name. -/
local macro "p63s% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

open scoped DC in
/-- Along a path `W` of `rho`, the bodies of `v`'s store in `W i` are bodies of its store in `W j`
    for `i ≤ j`. -/
private theorem bodies_mono_along₈₆cs (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {i j : Nat} (hij : i ≤ j) : (W i v).st.bodies ⊆ (W j v).st.bodies := by
  have hslice : W j ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) (W i) := by
    have h := (p62% onePath_reach₆₂s) W hW i (j - i)
    rwa [Nat.add_sub_of_le hij] at h
  exact Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho v hij (W i)
    (hW i).1 (W j) hslice

/-- Under the bundle, every event of `rho` whose index is less than `strictEventIndex rho t` is
    strictly before the instant `t`. -/
private theorem time_lt_of_lt_strictEventIndex₈₆cs (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  unfold strictEventIndex at hj
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt t)]
    exact List.mem_of_getElem? (by
      rw [List.getElem?_take_of_lt hj]
      exact he)
  have h := (List.mem_filter.mp hmem).2
  simpa only [decide_eq_true_eq] using h

/-- Under the bundle with path `W`, with every tick having an outcome, for a run-scoped named regime
    along `W` with `lo ≤ opening (a.round − η_SG)`, every member of the set for a read at or after
    `S.a a.round` holds the regime's FG source `Cfg` as a body of its store in the world of `W`
    strictly before the read. -/
theorem NamedHeightRegimeRunOn.sourceMem_at_read_l86c (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read)
    {w : V} (hw : w ∈ Hs read)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    Cfg ∈ (W (strictEventIndex rho read) w).st.bodies := by
  obtain ⟨hloEarly, -, -, -⟩ := Restated.loBounds_l70 facts S (h.seed.round_pos_l70 facts hf) hlo
  have hwView : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc a.round)) := by
    refine hHs _ _ ?_ hw
    obtain ⟨-, -, -, hview, -, ha⟩ := Restated.openingInstants_l63 facts S a.round
    rw [hview]
    have := S.E.Δ_pos
    linarith
  obtain ⟨nw, hnw⟩ := actionReadFrom_nonempty₈₆cn facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) w) a.round
  have hsource := h.seed.sourceMem_at_action_of_frame_named facts hf hHs hHsXb hX h.frame
    h.ready hwView hloEarly nw hnw
  rw [(p62% actionReadFrom_bodies₆₂s) facts S _ a.round nw hnw] at hsource
  exact bodies_mono_along₈₆cs facts S hf.onePath w (strict_filter_length_mono rho hread) hsource

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority and
    the weight bound, with `X` containing every set of the family from instant `0` and inside `Xb`,
    and `gstLagged ≤ Γ_neg1 r0`: if a run-scoped named base along `W` holds at `blocked`, a member
    of the set for its emission instant emits along `W` a row `b` at height `blocked + n + 1` whose
    FG source at a node state of its round's action read along `W` can return `Cfg`, `b.round ≤ c`,
    `S.a c` is in the horizon, `v` is in the set for `S.a c` and awake for round `c`, `C` is a run
    block read through `Xb` at height less than `blocked + n + 1` and an ancestor of a block `v`'s
    SG vote selector can return at a node state of its round-`c` action read along `W`, and the `lo`
    bounds hold, then `C` is an ancestor of `Cfg`. -/
theorem NamedHeightRegimeBaseRunOn.honestFGSource_preceq_of_actionSGBlock_ancestor
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
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ Hs tb)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {Cfg : Block V}
    {nb : M.N}
    (hnb : nb ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nb ⇢ some Cfg)
    {c : Round} (hbc : b.round ≤ c)
    (hchor : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon)
    {v : V} (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c))
    (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
    {C : NamedBlock V} (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {nv : M.N}
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G)
    (hCle : Block.Preceq C.erase G)
    (hheight : (M.derive_named S.E S.cfg C).h < blocked + n + 1)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.Preceq C.erase Cfg := by
  obtain ⟨first_n, i, a, ta, Cfg0, T, Tprev', c0, hreg⟩ :=
    Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb hX
      hXXb hcom hbelow hgst h n hb hemit hrow hgstLo hloOpen hA
  have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
  obtain ⟨D, K, hW, _hDmem, hsourceD, _hDheight, _hKmem, _hKerase, _hKheight, hKD, -⟩ :=
    Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf (hHsXb _ hb) hemit hrow
      nb hnb (some Cfg) hsource
  have hDCfg : D.erase = Cfg := (Option.some.inj hsourceD).symm
  have hTeq : T.erase = (M.derive_named S.E S.cfg K).T_h :=
    (Option.some.inj
      (Restated.NamedHeightRegimeRunOn.witness_eq facts hf hHs hHsXb hX hXXb hcom hbelow
        hreg hb hemit hrow hlo hA nb hnb _ hW)).symm
  have hac : a.round ≤ c := (hreg.minimal b tb hb hemit hrow).trans hbc
  obtain ⟨-, -, -, hloa⟩ :=
    Restated.loBounds_l70 facts S (hreg.seed.round_pos_l70 facts hf) hlo
  have hloc : lo ≤ Restated.Vocabulary.Execution.Setup.a M S c :=
    hloa.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hac)
  obtain ⟨Dv, hDv⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc
    (S.node v) nv.st nv.record
  have hSG : G.compatible T.erase = true :=
    Restated.NamedHeightRegimeRunOn.sgHistory_run_l86c facts hf hHs hHsXb hX
      hXXb hcom hbelow hreg hac hchor hlo hA v hv nv hnv Dv hDv
      (Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf c hv hchor hloc
        hAv (fun j hj => hf.tick_outcome j _ _ hj) nv hnv Dv hDv) A2 hA2 G hG
  have hCTor : Block.Preceq C.erase T.erase ∨ Block.Preceq T.erase C.erase := by
    rcases (show Block.Preceq G T.erase ∨ Block.Preceq T.erase G from
      compatible_cases hSG) with hST | hTS
    · exact Or.inl (preceq_trans_Preceq hCle hST)
    · exact preceq_linear_Preceq hCle hTS
  have hCT : Block.Preceq C.erase T.erase := by
    rcases hCTor with hCT | hTC
    · exact hCT
    · obtain ⟨hTrun, hTheight⟩ :=
        Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
      have hTCnamed : NamedBlock.Preceq T C :=
        Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hCrun hTC
      have hmono := facts.cs.derive_height_mono S.E S.cfg hTCnamed
      rw [hTheight] at hmono
      exact False.elim ((not_lt_of_ge hmono) hheight)
  rw [← hDCfg]
  rw [hTeq] at hCT
  exact preceq_trans_Preceq hCT
    (preceq_trans_Preceq (facts.csAdded.derive_named_T_h_preceq S.E S.cfg K) hKD)

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority and
    the weight bound, with `X` containing every set of the family from instant `0` and inside `Xb`,
    and `gstLagged ≤ Γ_neg1 r0`: if a run-scoped named base along `W` holds at `blocked`, `read` is
    in the horizon and at or before `S.a (c + 1)`, `S.a c` is in the horizon, `u` is in the set for
    the read, `v` is in the set for `S.a c` and awake for round `c`, `C` is a run block at height
    less than `blocked + n + 1` that is an ancestor of a block `v`'s SG vote selector can return at
    a node state of its round-`c` action read along `W` and a descendant of the finalized block of
    `u`'s store in the world of `W` strictly before the read, some body of that store has height
    greater than `blocked + n + 1`, and the `lo` bounds hold, then some run block `Y` of that
    store's tree at height `blocked + n + 1` is a descendant of `C`. -/
theorem NamedHeightRegimeBaseRunOn.exists_descendant_at_crossing_of_actionSGBlock_ancestor
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
    (n : Nat) {read : Time} (hhor : read ≤ rho.horizon)
    {c : Round} (hchor : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon)
    (hnext : read ≤ Restated.Vocabulary.Execution.Setup.a M S (c + 1))
    {u v : V} (hu : u ∈ Hs read) (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c))
    (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
    {C Xc : NamedBlock V} (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {nv : M.N}
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G)
    (hCle : Block.Preceq C.erase G)
    (hheight : (M.derive_named S.E S.cfg C).h < blocked + n + 1)
    (_hF : Block.Preceq (W (strictEventIndex rho read) u).st.core.F C.erase)
    (hXc : Xc ∈ (W (strictEventIndex rho read) u).st.bodies)
    (hcross : blocked + n + 1 < (M.derive_named S.E S.cfg Xc).h)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ Y : NamedBlock V, Restated.RunBlockOn M S rho W Xb Y ∧
      Y.erase ∈ (W (strictEventIndex rho read) u).st.core.T ∧
      Block.Preceq C.erase Y.erase ∧
      (M.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  obtain ⟨K, _hKX, _hKheight, Q, hQ, hwit⟩ :=
    facts.cs.height_crossing S.E S.cfg Xc
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHs⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum (hbelow read hhor) hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ := hwit p hpQ
  have hb : b.val_index ∈ Hs read := hbp ▸ hpHs
  have hbChain : b ∈ Protocol.named_chain_attestations Xc :=
    _root_.DecoupledConsensusModel.Sts.named_row_mem_chain_of_ancestor_source_l86c hcarrierX
      hbCarrier
  have hpast := time_lt_of_lt_strictEventIndex₈₆cs facts S Hs Xb hf read
  obtain ⟨j, tb, hjN, hjevent, _hjout, hemit⟩ :=
    Restated.honestCarriedAttestation_emittedBeforeIndexOn facts S Hs Xb hf hHs
      (fun j e hj he => (hpast j e hj he).le) hXc hbChain hb
  have htb : tb < read := hpast j (Record.Event.tick b.val_index tb) hjN hjevent
  have hbT : b.val_index ∈ Hs tb := hHs _ _ htb.le hb
  have hread : Restated.Vocabulary.Execution.Setup.a M S b.round < read := by
    rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2]
    exact htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    _root_.DecoupledConsensusModel.Sts.named_height_of_matches_source_l86c hpair
  have hbc : b.round ≤ c :=
    Nat.le_of_lt_succ
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).lt_iff_lt.mp
        (hread.trans_le hnext))
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb hX
      hXXb hcom hbelow hgst h n hbT hemit hrow hgstLo hloOpen hA
  have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
  have hseedRow : a.height_pair.erase.height? = some (blocked + n + 1) := by
    rcases hreg.seed.targetOrTimeout with heq | heq <;>
      simp only [heq, HeightPair.height?, Nat.add_assoc]
  have hab : a.round ≤ b.round := hreg.minimal b tb hbT hemit hrow
  have hac : a.round ≤ c := hab.trans hbc
  obtain ⟨na, hna⟩ := actionReadFrom_nonempty₈₆cn facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨o, ho⟩ := (p63s% actionFGSource_nonempty₆₃w) facts S na
  have hoCfg : o = some Cfg.erase := hreg.seed.exactFGSource na hna o ho
  have hCCfg :=
    Restated.NamedHeightRegimeBaseRunOn.honestFGSource_preceq_of_actionSGBlock_ancestor facts
      hf hHs hHsXb hX hXXb hcom hbelow hgst h n hreg.seed.signerHonest hreg.seed.emitted
      hseedRow hna (hoCfg ▸ ho) hac hchor hv hAv hCrun hnv hA2 hG hCle hheight hgstLo hloOpen hA
  have haRead : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read :=
    ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hab).trans
      hread.le
  have hCfgRead : Cfg ∈ (W (strictEventIndex rho read) u).st.bodies :=
    Restated.NamedHeightRegimeRunOn.sourceMem_at_read_l86c facts hf hHs hHsXb hX hreg
      haRead hu hlo
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho read
    u _ ((p62% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath read)).1.1.1
  have hCfgErased : Cfg.erase ∈ (W (strictEventIndex rho read) u).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hCfgRead
  exact ⟨Cfg,
    Restated.runHistory_actionBody_runBlockOn facts S Hs Xb hf
      (hHsXb _ hreg.seed.signerHonest)
      hna (hreg.seed.sourceMem na hna),
    hCfgErased, hCCfg, hreg.seed.sourceDerivedHeight⟩

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority and
    the weight bound, with `X` containing every set of the family from instant `0` and inside `Xb`,
    and `gstLagged ≤ Γ_neg1 r0`: if a run-scoped named base along `W` holds at `blocked` whose first
    crossing is by the inclusive index of `S.a deadline`, `deadline ≤ c`, `S.a c` is in the horizon,
    the read is from `S.a deadline` to `S.a (c + 1)` within the horizon, `u` is in the set for the
    read, `v` is in the set for `S.a c` and awake for round `c`, `C` is a run block that is an
    ancestor of a block `v`'s SG vote selector can return at a node state of its round-`c` action
    read along `W` and a body of `u`'s store in the world of `W` strictly before the read, and the
    `lo` bounds hold, then `C` is in the filtered tree of that store or an ancestor of its FG root. -/
theorem NamedHeightRegimeBaseRunOn.filteredMem_or_preceq_root_of_actionSGBlock_ancestor
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
    (hchor : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon)
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S deadline ≤ read)
    (hhor : read ≤ rho.horizon)
    (hnext : read ≤ Restated.Vocabulary.Execution.Setup.a M S (c + 1))
    {u v : V} (hu : u ∈ Hs read) (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c))
    (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
    {C : NamedBlock V} (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {nv : M.N}
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G)
    (hCle : Block.Preceq C.erase G)
    (hCbody : C ∈ (W (strictEventIndex rho read) u).st.bodies)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    C.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG ∨
      Block.Preceq C.erase
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) := by
  have hwmem := (p62% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath read
  have hcompatVote :=
    Restated.NamedHeightRegimeBaseRunOn.fgRoot_compatible_actionSGBlock_at_read_after_deadline_l86c
      facts hf hHs hHsXb hX hXXb hcom hbelow hgst h hdeadline hc hchor hread hhor hnext
      hu hv hAv hgstLo hloOpen hA nv hnv A2 hA2 G hG
  have hrootCases :
      Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) C.erase ∨
        Block.Preceq C.erase
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) := by
    rcases compatible_cases hcompatVote with hrv | hvr
    · exact preceq_linear_Preceq hrv hCle
    · exact Or.inr (preceq_trans_Preceq hCle hvr)
  rcases hrootCases with hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg0, T, hreg, ha⟩ :=
      Restated.NamedHeightRegimeBaseRunOn.exists_regime_before_deadline facts hf hHs
        hHsXb hX hXXb hbelow hgst h hgstLo hloOpen hdeadline
    have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
    have hac : a.round ≤ c := ha.trans hc
    have hrootMem :=
      Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S
        rho read u _ hwmem
    have hFroot : Block.Preceq (W (strictEventIndex rho read) u).st.core.F
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) := by
      have h0 := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hrootMem
      rw [facts.sto.ModelProperties_toHealing_F] at h0
      exact h0
    have hFC : Block.Preceq (W (strictEventIndex rho read) u).st.core.F C.erase :=
      preceq_trans_Preceq hFroot hroot
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      read u _ hwmem).1.1.1
    have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S
      rho read u _ hwmem
    have hCmem : C.erase ∈ (W (strictEventIndex rho read) u).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hCbody
    have hstoredC : ((W (strictEventIndex rho read) u).st.core.σ C.erase).h =
        (M.derive_named S.E S.cfg C).h := by
      rw [hview C hCbody]
    have hwitness : ∃ Y ∈ (W (strictEventIndex rho read) u).st.core.T,
        Block.Preceq C.erase Y ∧
          (W (strictEventIndex rho read) u).st.core.h_max - 1 ≤
            ((W (strictEventIndex rho read) u).st.core.σ Y).h := by
      by_cases hcap : (W (strictEventIndex rho read) u).st.core.h_max ≤
          (M.derive_named S.E S.cfg C).h + 1
      · refine ⟨C.erase, hCmem, Proofs.ModelProperties.Preceq_self C.erase, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (M.derive_named S.E S.cfg C).h + 1 <
            (W (strictEventIndex rho read) u).st.core.h_max := Nat.lt_of_not_le hcap
        have hCH : (M.derive_named S.E S.cfg C).h <
            (W (strictEventIndex rho read) u).st.core.h_max - 1 := Nat.lt_sub_of_add_lt hlt
        by_cases hlow : (W (strictEventIndex rho read) u).st.core.h_max - 1 ≤ blocked + 1
        · have hrow : a.height_pair.erase.height? = some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          obtain ⟨na, hna⟩ := actionReadFrom_nonempty₈₆cn facts S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
              a.val_index) a.round
          obtain ⟨o, ho⟩ := (p63s% actionFGSource_nonempty₆₃w) facts S na
          have hoCfg : o = some Cfg0.erase := hreg.seed.exactFGSource na hna o ho
          have hCCfg :=
            Restated.NamedHeightRegimeBaseRunOn.honestFGSource_preceq_of_actionSGBlock_ancestor
              facts hf hHs hHsXb hX hXXb hcom hbelow hgst h 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hna (hoCfg ▸ ho) hac hchor hv hAv hCrun hnv hA2 hG hCle
              (hCH.trans_le hlow) hgstLo hloOpen hA
          have hCfgBody : Cfg0 ∈ (W (strictEventIndex rho read) u).st.bodies :=
            Restated.NamedHeightRegimeRunOn.sourceMem_at_read_l86c facts hf hHs hHsXb hX
              hreg
              (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
                ha).trans hread) hu hlo
          have hCfgMem : Cfg0.erase ∈ (W (strictEventIndex rho read) u).st.core.T := by
            rw [hcoh.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgBody
          refine ⟨Cfg0.erase, hCfgMem, hCCfg, ?_⟩
          rw [hview Cfg0 hCfgBody, hreg.seed.sourceDerivedHeight]
          exact hlow
        · have heq : blocked +
              ((W (strictEventIndex rho read) u).st.core.h_max - 1 - (blocked + 1)) + 1 =
              (W (strictEventIndex rho read) u).st.core.h_max - 1 := by
            calc
              _ = ((W (strictEventIndex rho read) u).st.core.h_max - 1 - (blocked + 1)) +
                  (blocked + 1) := by ac_rfl
              _ = (W (strictEventIndex rho read) u).st.core.h_max - 1 :=
                Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨Xm, hXbody, hXmax⟩ :=
            Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime facts S rho
              read u _ hwmem
          have hmaxPos : (W (strictEventIndex rho read) u).st.core.h_max ≠ 0 := Nat.ne_of_gt
            ((Nat.zero_le ((M.derive_named S.E S.cfg C).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYmem, hCY, hYheight⟩ :=
            Restated.NamedHeightRegimeBaseRunOn.exists_descendant_at_crossing_of_actionSGBlock_ancestor
              facts hf hHs hHsXb hX hXXb hcom hbelow hgst h
              ((W (strictEventIndex rho read) u).st.core.h_max - 1 - (blocked + 1))
              hhor hchor hnext hu hv hAv hCrun hnv hA2 hG hCle
              (by rw [heq]; exact hCH) hFC hXbody
              (by
                rw [heq, hXmax]
                exact Nat.sub_one_lt hmaxPos)
              hgstLo hloOpen hA
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S
              rho read u _ hwmem hYmem
          have hYnrun : Restated.RunBlockOn M S rho W Xb Yn :=
            Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu)
              hYnbody
          have hYnY : Yn = Y := by
            apply hf.rootCollisionFree.root_injective Yn Y hYnrun hYrun Yn Y
              (Or.inl (Proofs.NamedAncestry.named_self Yn))
              (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase, Proofs.NamedWire.erase_root]
          subst Yn
          refine ⟨Y.erase, hYmem, hCY, ?_⟩
          rw [hview Y hYnbody, hYheight, heq]
    obtain ⟨Y, hYT, hCY, hYh⟩ := hwitness
    exact facts.fc.mem_get_filtered_block_tree_of_parts
      (M.toHealing (W (strictEventIndex rho read) u).st.core)
      (by rw [facts.sto.toHealing_gs_T]; exact hCmem)
      (by rw [facts.sto.ModelProperties_toHealing_F]; exact hFC)
      (by rw [facts.sto.toHealing_gs_T]; exact hYT) hCY
      (by
        rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]
        exact hYh) hroot
  · exact Or.inr hroot

/-- Under the premises of `fgRoot_compatible_actionSGBlock_at_read_after_GSTOn_l86c`, a run block
    `C` that is an ancestor of a block `v`'s SG vote selector can return at a node state of its
    round-`c` action read along `W` and a body of `u`'s store in the world of `W` strictly before
    the read is in the filtered tree of that store or an ancestor of its FG root. -/
theorem actionSGBlock_filteredMem_or_preceq_root_after_GST_ancestorOn (facts : Record.Facts M)
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
    (hchor : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ rho.horizon)
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hhor : read ≤ rho.horizon)
    (hnext : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)))
    {u v : V} (hu : u ∈ Hs read)
    (hv : v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c))
    (hAv : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S c)) → M.awake_for_grade2 S v (W j v) c)
    {C : NamedBlock V} (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {nv : M.N}
    (hnv : nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    {A2 : Option (Block V)}
    (hA2 : M.grade2_block_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) ⇢ A2)
    {G : Block V}
    (hG : M.get_sg_vote_with (M.gradeContract nv.cache) S.E S.hc (M.toHealing nv.st.core)
      (M.round_of S.hc (M.toHealing nv.st.core).s) A2 ⇢ G)
    (hCle : Block.Preceq C.erase G)
    (hCbody : C ∈ (W (strictEventIndex rho read) u).st.bodies)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    C.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG ∨
      Block.Preceq C.erase
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) u).st.core).toFG) := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost (hread.trans hhor)
      hlo hloOpen ht₀ hA
  exact Restated.NamedHeightRegimeBaseRunOn.filteredMem_or_preceq_root_of_actionSGBlock_ancestor
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hc hchor hread hhor hnext hu hv hAv hCrun hnv hA2 hG hCle hCbody
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

end

/-! ## The candidate tree or the FG root, against a previous head -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_60.lean`, by name. -/
local macro "p60c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_60)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_62.lean`, by name. -/
local macro "p62c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_62)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- A private theorem of the page `lean/Proofs/Claims/Restated/Claim13beRoute3_63.lean`, by name. -/
local macro "p63c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The action instant of round `r` is at or before the view freeze of every slot after round `r`'s
    opening slot. -/
private theorem action_le_view_freeze_of_slot₈₆cp (facts : Record.Facts M) (S : Setup V)
    {r : Round} {s : Slot} (h : M.opening_slot S.hc r + 1 ≤ s) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤ M.view_freeze S.E s := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ =
      M.view_freeze S.E (M.opening_slot S.hc r + 1) := facts.sch.a_add_delta_eq_view_freeze S r
  have hd := S.E.Δ_pos
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [← heq]
    linarith
  · have h2 := facts.sch.view_freeze_lt_vote_time_succ S.E (M.opening_slot S.hc r + 1)
    have h3 := facts.sch.vote_time_mono_slots S.E (Nat.succ_le_of_lt hlt)
    have h4 := facts.sch.vote_time_le_view_freeze S.E s
    linarith

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority and
    the weight bound, with `X` containing every set of the family from instant `0` and inside `Xb`,
    and `gstLagged ≤ Γ_neg1 r0`: if a run-scoped named base along `W` holds at `blocked`, a member
    of the set for its emission instant emits along `W` a row `b` at height `blocked + n + 1` whose
    FG source at a node state of its round's action read along `W` can return `Cfg`, `s` is after
    the opening slot of `b`'s round with `vote_time s + Δ` in the horizon, `v` is in the set for
    `vote_time s`, `C` is a run block read through `Xb` at height less than `blocked + n + 1` and an
    ancestor of a head `v`'s vote-duty read of slot `s` along `W` can return, and the `lo` bounds
    hold, then `C` is an ancestor of `Cfg`. -/
theorem NamedHeightRegimeBaseRunOn.honestFGSource_preceq_of_previousHead
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
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ Hs tb)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    {Cfg : Block V}
    {nb : M.N}
    (hnb : nb ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nb ⇢ some Cfg)
    {s : Slot} (hs : M.opening_slot S.hc b.round + 1 ≤ s)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s)) {C : NamedBlock V}
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {cc : M.Cache}
    (hcc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cc)
    {Tr : Finset (Block V)}
    (hTr : M.voter_filtered_block_tree S.E
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ Tr)
    {L : Finset (GoldfishVote V)}
    (hL : M.voter_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L)
    {L' : Finset (GoldfishVote V)}
    (hL' : M.voter_support_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L')
    {H : Block V}
    (hH : M.get_head_in_tree_with_layer
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).cache) S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core) Tr L L'
      ((M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s - 1) ⇢ H)
    (hC : Block.Preceq C.erase H)
    (hheight : (M.derive_named S.E S.cfg C).h < blocked + n + 1)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.Preceq C.erase Cfg := by
  obtain ⟨first_n, i, a, ta, Cfg0, T, Tprev', c0, hreg⟩ :=
    Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb hX
      hXXb hcom hbelow hgst h n hb hemit hrow hgstLo hloOpen hA
  have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
  obtain ⟨D, K, hW, _hDmem, hsourceD, _hDheight, _hKmem, _hKerase, _hKheight, hKD, -⟩ :=
    Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf (hHsXb _ hb) hemit hrow
      nb hnb (some Cfg) hsource
  have hDCfg : D.erase = Cfg := (Option.some.inj hsourceD).symm
  have hTeq : T.erase = (M.derive_named S.E S.cfg K).T_h :=
    (Option.some.inj
      (Restated.NamedHeightRegimeRunOn.witness_eq facts hf hHs hHsXb hX hXXb hcom hbelow
        hreg hb hemit hrow hlo hA nb hnb _ hW)).symm
  have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
  have hopen : M.opening_slot S.hc a.round + 1 ≤ s :=
    (Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc hab) 1).trans hs
  have hheads : Block.Preceq T.erase H :=
    Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX hXXb
      hcom hbelow hreg hopen hshor hlo hA v hv cc hcc Tr hTr L hL L' hL' H hH
  have hCT : Block.Preceq C.erase T.erase := by
    rcases preceq_linear_Preceq hC hheads with hCT | hTC
    · exact hCT
    · obtain ⟨hTrun, hTheight⟩ :=
        Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
      have hTCnamed : NamedBlock.Preceq T C :=
        Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTrun hCrun hTC
      have hmono := facts.cs.derive_height_mono S.E S.cfg hTCnamed
      rw [hTheight] at hmono
      exact False.elim ((not_lt_of_ge hmono) hheight)
  rw [← hDCfg]
  rw [hTeq] at hCT
  exact preceq_trans_Preceq hCT
    (preceq_trans_Preceq (facts.csAdded.derive_named_T_h_preceq S.E S.cfg K) hKD)

/-- `vote_time s + Δ ≤ vote_time (s + 1)`. -/
theorem vote_add_delta_le_nextVote_l86c (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s + E.Δ ≤ M.vote_time E (s + 1) := by
  obtain ⟨h1, -, -, -, h5, -⟩ := facts.sch.slot_instants_l55 E s
  have hd := E.Δ_pos
  rw [h1, h5]
  linarith

/-- Under the bundle with path `W`, if `1 ≤ s` and `B` is in the tree of `u`'s store in the world of
    `W` strictly before the view freeze of `s − 1`, then `B` is in every outcome of the processed
    tree, at slot `s`, of every node state `u`'s vote-duty read of slot `s` along `W` can give. -/
theorem voterProcessed_mem_of_mem_previousFreeze_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 1 ≤ s) {u : V} {B : Block V}
    (hB : B ∈ (W (strictEventIndex rho (M.view_freeze S.E (s - 1))) u).st.core.T) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) u).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) u).cache ⇢ cc →
      ∀ P : Finset (Block V),
        M.voter_processed_block_tree S.E
          (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) u).st
              (M.vote_time S.E s))
            (W (strictEventIndex rho (M.vote_time S.E s)) u).record
            cc).st.core).toFG.toSG.toGoldfishStore s ⇢ P →
        B ∈ P := by
  intro cc _hcc P hP
  have hfreeze : M.view_freeze S.E (s - 1) < M.vote_time S.E s := by
    have h := facts.sch.view_freeze_lt_vote_time_succ S.E (s - 1)
    rwa [Nat.sub_add_cancel hs] at h
  have htransport :
      B ∈ (W (strictEventIndex rho (M.vote_time S.E s)) u).st.T ∧
        stampedBefore (W (strictEventIndex rho (M.vote_time S.E s)) u).st.timestamp_block
          (M.view_freeze S.E (s - 1)) B = true := by
    rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts S Hs Xb hf u
        _ hB with hgen | ⟨D, i, t, hDerase, hacc, ht⟩
    · subst B
      exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf u _ _
    · exact Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf
        ⟨D, hDerase, i, t, hacc, ht⟩ hfreeze.le
  refine facts.fc.mem_voter_processed_block_tree_of_stamped _ _ _ ?_ ?_ P hP
  · rewrite [facts.sto.toHealing_gs_T, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
    exact htransport.1
  · rewrite [facts.sto.toHealing_gs_timestamp_block, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_timestamp_block]
    exact htransport.2

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority and
    the weight bound, with `X` containing every set of the family from instant `0` and inside `Xb`,
    and `gstLagged ≤ Γ_neg1 r0`: if a run-scoped named base along `W` holds at `blocked`,
    `vote_time (s + 1)` and `vote_time s + Δ` are in the horizon, `u` is in the set for
    `vote_time (s + 1)`, `v` is in the set for `vote_time s`, `C` is a run block at height less than
    `blocked + n + 1` that is an ancestor of a head `v`'s vote-duty read of slot `s` along `W` can
    return, some body of a node state of `u`'s vote-duty read of slot `s + 1` along `W` has height
    greater than `blocked + n + 1`, and the `lo` bounds hold, then for every outcome `P` of the
    processed tree of that node state at slot `s + 1`, some run block `Y` in `P` at height
    `blocked + n + 1` is a descendant of `C`. -/
theorem NamedHeightRegimeBaseRunOn.exists_frozen_descendant_at_crossing_of_previousHead_named
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
    (n : Nat) {s : Slot}
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ Hs (M.vote_time S.E (s + 1)))
    (hv : v ∈ Hs (M.vote_time S.E s))
    {C Xc : NamedBlock V} (hCrun : Restated.RunBlockOn M S rho W Xb C)
    {cc : M.Cache}
    (hcc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cc)
    {Tr : Finset (Block V)}
    (hTr : M.voter_filtered_block_tree S.E
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ Tr)
    {L : Finset (GoldfishVote V)}
    (hL : M.voter_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L)
    {L' : Finset (GoldfishVote V)}
    (hL' : M.voter_support_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L')
    {H : Block V}
    (hH : M.get_head_in_tree_with_layer
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).cache) S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core) Tr L L'
      ((M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s - 1) ⇢ H)
    (hC : Block.Preceq C.erase H)
    (hheight : (M.derive_named S.E S.cfg C).h < blocked + n + 1)
    {cu : M.Cache}
    (hcu : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).cache ⇢ cu)
    (hXc : Xc ∈ (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu).st.bodies)
    (hcross : blocked + n + 1 < (M.derive_named S.E S.cfg Xc).h)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ P : Finset (Block V),
      M.voter_processed_block_tree S.E
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record
          cu).st.core).toFG.toSG.toGoldfishStore (s + 1) ⇢ P →
      ∃ Y : NamedBlock V, Restated.RunBlockOn M S rho W Xb Y ∧
        Y.erase ∈ P ∧
        Block.Preceq C.erase Y.erase ∧
        (M.derive_named S.E S.cfg Y).h = blocked + n + 1 := by
  intro P hP
  obtain ⟨K, _hKX, _hKheight, Q, hQ, hwit⟩ :=
    facts.cs.height_crossing S.E S.cfg Xc
      (blocked + n + 1) (Nat.succ_le_succ (Nat.zero_le _)) hcross
  obtain ⟨p, hpQ, hpHs⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum (hbelow _ hhor) hQ
  obtain ⟨carrier, b, hcarrierX, hbCarrier, hbp, hpair⟩ := hwit p hpQ
  have hb : b.val_index ∈ Hs (M.vote_time S.E (s + 1)) := hbp ▸ hpHs
  have hbChain : b ∈ Protocol.named_chain_attestations Xc :=
    _root_.DecoupledConsensusModel.Sts.named_row_mem_chain_of_ancestor_source_l86c hcarrierX
      hbCarrier
  have hXread : Xc ∈ (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.bodies := by
    have h0 := hXc
    rewrite [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies] at h0
    rw [facts.hd.Sts_setClock_bodies] at h0
    exact h0
  have hpast := time_lt_of_lt_strictEventIndex₈₆cs facts S Hs Xb hf (M.vote_time S.E (s + 1))
  obtain ⟨j, tb, hjN, hjevent, _hjout, hemit⟩ :=
    Restated.honestCarriedAttestation_emittedBeforeIndexOn facts S Hs Xb hf hHs
      (fun j e hj he => (hpast j e hj he).le) hXread hbChain hb
  have htb : tb < M.vote_time S.E (s + 1) := hpast j (Record.Event.tick b.val_index tb) hjN hjevent
  have hbT : b.val_index ∈ Hs tb := hHs _ _ htb.le hb
  have hread : Restated.Vocabulary.Execution.Setup.a M S b.round < M.vote_time S.E (s + 1) := by
    rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2]
    exact htb
  have hrow : b.height_pair.erase.height? = some (blocked + n + 1) :=
    _root_.DecoupledConsensusModel.Sts.named_height_of_matches_source_l86c hpair
  obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
    Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named facts hf hHs hHsXb hX
      hXXb hcom hbelow hgst h n hbT hemit hrow hgstLo hloOpen hA
  have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
  have hseedRow : a.height_pair.erase.height? = some (blocked + n + 1) := by
    rcases hreg.seed.targetOrTimeout with heq | heq <;>
      simp only [heq, HeightPair.height?, Nat.add_assoc]
  have hab : a.round ≤ b.round := hreg.minimal b tb hbT hemit hrow
  have hbSlot : M.opening_slot S.hc b.round + 1 ≤ s := by
    by_contra hn
    have hslot : s + 1 ≤ M.opening_slot S.hc b.round + 1 :=
      Nat.succ_le_succ (Nat.le_of_lt_succ (Nat.lt_of_not_ge hn))
    have htime := facts.sch.vote_time_mono_slots S.E hslot
    exact (not_lt_of_ge htime)
      ((Restated.Vocabulary.Protocol.next_vote_time_lt_action facts S b.round).trans hread)
  have haSlot : M.opening_slot S.hc a.round + 1 ≤ s :=
    (Nat.add_le_add_right (facts.gr.opening_slot_mono S hab) 1).trans hbSlot
  obtain ⟨na, hna⟩ := actionReadFrom_nonempty₈₆cn facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨o, ho⟩ := (p63c% actionFGSource_nonempty₆₃w) facts S na
  have hoCfg : o = some Cfg.erase := hreg.seed.exactFGSource na hna o ho
  have hCCfg :=
    Restated.NamedHeightRegimeBaseRunOn.honestFGSource_preceq_of_previousHead facts
      hf hHs hHsXb hX hXXb hcom hbelow hgst h n hreg.seed.signerHonest hreg.seed.emitted
      hseedRow hna (hoCfg ▸ ho) haSlot hshor hv hCrun hcc hTr hL hL' hH hC hheight hgstLo hloOpen
      hA
  have haFreeze : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ M.view_freeze S.E s :=
    action_le_view_freeze_of_slot₈₆cp facts S haSlot
  have huFreeze : u ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E s).le hu
  have hCfgFreezeBody : Cfg ∈ (W (strictEventIndex rho (M.view_freeze S.E s)) u).st.bodies :=
    Restated.NamedHeightRegimeRunOn.sourceMem_at_read_l86c facts hf hHs hHsXb hX hreg
      haFreeze huFreeze hlo
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
    (M.view_freeze S.E s) u _
    ((p62c% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath (M.view_freeze S.E s))).1.1.1
  have hCfgFreeze : Cfg.erase ∈
      (W (strictEventIndex rho (M.view_freeze S.E (s + 1 - 1))) u).st.core.T := by
    rw [Nat.add_sub_cancel, hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hCfgFreezeBody
  have hCfgProcessed :=
    Restated.voterProcessed_mem_of_mem_previousFreeze_namedOn facts S Hs Xb hf
      (s := s + 1) (Nat.succ_le_succ (Nat.zero_le s)) hCfgFreeze cu hcu P hP
  exact ⟨Cfg,
    Restated.runHistory_actionBody_runBlockOn facts S Hs Xb hf
      (hHsXb _ hreg.seed.signerHonest)
      hna (hreg.seed.sourceMem na hna),
    hCfgProcessed, hCCfg, hreg.seed.sourceDerivedHeight⟩

/-- Under the bundle with path `W`, with every tick having an outcome, the committee majority and
    the weight bound, with `X` containing every set of the family from instant `0` and inside `Xb`,
    and `gstLagged ≤ Γ_neg1 r0`: if a run-scoped named base along `W` holds at `blocked` whose first
    crossing is by the inclusive index of `S.a deadline`, `s` is after the deadline's opening slot,
    `vote_time (s + 1)` is in the horizon, `u` is in the set for `vote_time (s + 1)`, `v` is in the
    set for `vote_time s`, `C` is an ancestor of a head `v`'s vote-duty read of slot `s` along `W`
    can return and is in an outcome of the processed tree of a node state of `u`'s vote-duty read of
    slot `s + 1` along `W`, and the `lo` bounds hold, then for every outcome `Tu` of the candidate
    tree of that node state, `C` is in `Tu` or is an ancestor of that node state's FG root. -/
theorem NamedHeightRegimeBaseRunOn.voterCandidateMem_or_preceq_root_of_honestPreviousHead_named
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
    {s : Slot} (hs : M.opening_slot S.hc deadline + 1 ≤ s)
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    {u v : V} (hu : u ∈ Hs (M.vote_time S.E (s + 1)))
    (hv : v ∈ Hs (M.vote_time S.E s))
    {C : Block V}
    {cc : M.Cache}
    (hcc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cc)
    {Tr : Finset (Block V)}
    (hTr : M.voter_filtered_block_tree S.E
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ Tr)
    {L : Finset (GoldfishVote V)}
    (hL : M.voter_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L)
    {L' : Finset (GoldfishVote V)}
    (hL' : M.voter_support_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L')
    {H : Block V}
    (hH : M.get_head_in_tree_with_layer
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).cache) S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core) Tr L L'
      ((M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s - 1) ⇢ H)
    (hC : Block.Preceq C H)
    {cu : M.Cache}
    (hcu : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).cache ⇢ cu)
    {P : Finset (Block V)}
    (hP : M.voter_processed_block_tree S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record
        cu).st.core).toFG.toSG.toGoldfishStore (s + 1) ⇢ P)
    (hCmem : C ∈ P)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ Tu : Finset (Block V),
      M.voter_filtered_block_tree S.E
        (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu).st.core
        (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu).st.core.s ⇢ Tu →
      C ∈ Tu ∨
        Block.Preceq C
          (M.get_fg_root (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record
            cu).st.core).toFG) := by
  intro Tu hTu
  have hst := facts.nd.mkNode_st
    (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
      (M.vote_time S.E (s + 1)))
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu
  have hP0 := hP
  rw [hst] at hP hTu ⊢
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hP hTu ⊢
  have hrootEq := (p60c% setClock_fgRoot₆₀) facts S
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st (M.vote_time S.E (s + 1))
  rw [hrootEq]
  have hdeadlineVote : Restated.Vocabulary.Execution.Setup.a M S deadline <
      M.vote_time S.E (s + 1) :=
    (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S deadline).trans_le
      (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_succ hs))
  have hdeadlineFreeze : Restated.Vocabulary.Execution.Setup.a M S deadline ≤
      M.view_freeze S.E s := action_le_view_freeze_of_slot₈₆cp facts S hs
  have hshor := (Restated.vote_add_delta_le_nextVote_l86c facts S.E s).trans hhor
  have hbound : M.vote_time S.E (s + 1) ≤ M.confirmation_time S.E s :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)
  have hrootHead : Block.Preceq
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core).toFG) H :=
    Restated.NamedHeightRegimeBaseRunOn.fgRoot_preceq_previousHead_through_confirmation_after_deadline
      facts hf hHs hHsXb hX hXXb hcom hbelow hgst h hdeadline hdeadlineVote.le hhor hs
      hbound hshor hu hgstLo hloOpen hA v hv cc hcc Tr hTr L hL L' hL' H hH
  rcases preceq_linear_Preceq hrootHead hC with hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
      Restated.NamedHeightRegimeBaseRunOn.exists_regime_before_deadline facts hf hHs
        hHsXb hX hXXb hbelow hgst h hgstLo hloOpen hdeadline
    have hlo := Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen
    have hwmem := (p62c% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath
      (M.vote_time S.E (s + 1))
    have hrootMem :=
      Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S
        rho (M.vote_time S.E (s + 1)) u _ hwmem
    have hFroot : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.F
        (M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core).toFG) := by
      have h0 := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hrootMem
      rw [facts.sto.ModelProperties_toHealing_F] at h0
      exact h0
    have hFC : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.F C :=
      preceq_trans_Preceq hFroot hroot
    have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S
      rho (M.vote_time S.E (s + 1)) u _ hwmem
    have hTmem : ∀ {Z : Block V}, Z ∈ P →
        Z ∈ (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.T := by
      intro Z hZ
      have h0 := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ P hP hZ
      rw [facts.sto.toHealing_gs_T, facts.hd.Sts_setClock_core_T] at h0
      exact h0
    obtain ⟨Cn, hCnbody, hCnerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S
        rho (M.vote_time S.E (s + 1)) u _ hwmem (hTmem hCmem)
    have hCnrun : Restated.RunBlockOn M S rho W Xb Cn :=
      Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu) hCnbody
    have hstoredC : ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.σ C).h =
        (M.derive_named S.E S.cfg Cn).h := by
      rw [← hCnerase, hview Cn hCnbody]
    have hCnH : Block.Preceq Cn.erase H := by rw [hCnerase]; exact hC
    have hwitness : ∃ Y ∈ P, Block.Preceq C Y ∧
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 ≤
          ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.σ Y).h := by
      by_cases hcap : (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max ≤
          (M.derive_named S.E S.cfg Cn).h + 1
      · refine ⟨C, hCmem, Proofs.ModelProperties.Preceq_self C, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (M.derive_named S.E S.cfg Cn).h + 1 <
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max :=
          Nat.lt_of_not_le hcap
        have hCH : (M.derive_named S.E S.cfg Cn).h <
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 :=
          Nat.lt_sub_of_add_lt hlt
        by_cases hlow : (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 ≤
            blocked + 1
        · have hrow : a.height_pair.erase.height? = some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          have hopen : M.opening_slot S.hc a.round + 1 ≤ s :=
            (Nat.add_le_add_right (facts.gr.opening_slot_le_of_le S.hc ha) 1).trans hs
          obtain ⟨na, hna⟩ := actionReadFrom_nonempty₈₆cn facts S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
              a.val_index) a.round
          obtain ⟨o, ho⟩ := (p63c% actionFGSource_nonempty₆₃w) facts S na
          have hoCfg : o = some Cfg.erase := hreg.seed.exactFGSource na hna o ho
          have hCCfg :=
            Restated.NamedHeightRegimeBaseRunOn.honestFGSource_preceq_of_previousHead facts
              hf hHs hHsXb hX hXXb hcom hbelow hgst h 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hna (hoCfg ▸ ho) hopen hshor hv hCnrun hcc hTr hL hL' hH
              hCnH (hCH.trans_le hlow) hgstLo hloOpen hA
          have haFreeze : Restated.Vocabulary.Execution.Setup.a M S a.round ≤
              M.view_freeze S.E s :=
            ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
              ha).trans hdeadlineFreeze
          have huFreeze : u ∈ Hs (M.view_freeze S.E s) :=
            hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E s).le hu
          have hCfgFreezeBody :=
            Restated.NamedHeightRegimeRunOn.sourceMem_at_read_l86c facts hf hHs hHsXb hX
              hreg haFreeze huFreeze hlo
          have hcohFreeze := (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants
            facts S rho (M.view_freeze S.E s) u _
            ((p62c% mem_stateBeforeTime_along₆₂s) hf.sorted hf.onePath
              (M.view_freeze S.E s))).1.1.1
          have hCfgFreeze : Cfg.erase ∈
              (W (strictEventIndex rho (M.view_freeze S.E (s + 1 - 1))) u).st.core.T := by
            rw [Nat.add_sub_cancel, hcohFreeze.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgFreezeBody
          have hCfgProcessed :=
            Restated.voterProcessed_mem_of_mem_previousFreeze_namedOn facts S Hs Xb hf
              (s := s + 1) (Nat.succ_le_succ (Nat.zero_le s)) hCfgFreeze cu hcu P hP0
          have hCfgReadBody :=
            Restated.NamedHeightRegimeRunOn.sourceMem_at_read_l86c facts hf hHs hHsXb hX
              hreg
              (((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
                ha).trans hdeadlineVote.le) hu hlo
          refine ⟨Cfg.erase, hCfgProcessed, ?_, ?_⟩
          · rw [← hCnerase]
            exact hCCfg
          · rw [hview Cfg hCfgReadBody, hreg.seed.sourceDerivedHeight]
            exact hlow
        · have heq : blocked +
              ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 -
                (blocked + 1)) + 1 =
              (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 := by
            calc
              _ = ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 -
                  (blocked + 1)) + (blocked + 1) := by ac_rfl
              _ = (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 :=
                Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨Xm, hXbody, hXmax⟩ :=
            Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime facts S rho
              (M.vote_time S.E (s + 1)) u _ hwmem
          have hXread : Xm ∈ (M.mkNode
              (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
                (M.vote_time S.E (s + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu).st.bodies := by
            rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies, facts.hd.Sts_setClock_bodies]
            exact hXbody
          have hmaxPos : (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max ≠ 0 :=
            Nat.ne_of_gt ((Nat.zero_le ((M.derive_named S.E S.cfg Cn).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYprocessed, hCY, hYheight⟩ :=
            Restated.NamedHeightRegimeBaseRunOn.exists_frozen_descendant_at_crossing_of_previousHead_named
              facts hf hHs hHsXb hX hXXb hcom hbelow hgst h
              ((W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.h_max - 1 -
                (blocked + 1))
              hhor hshor hu hv hCnrun hcc hTr hL hL' hH hCnH
              (by rw [heq]; exact hCH) hcu hXread
              (by
                rw [heq, hXmax]
                exact Nat.sub_one_lt hmaxPos)
              hgstLo hloOpen hA P hP0
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S
              rho (M.vote_time S.E (s + 1)) u _ hwmem (hTmem hYprocessed)
          have hYnrun : Restated.RunBlockOn M S rho W Xb Yn :=
            Restated.lifecycle_runBlock_of_mem_storeBeforeTimeOn facts S Hs Xb hf (hHsXb _ hu)
              hYnbody
          have hYnY : Yn = Y := by
            apply hf.rootCollisionFree.root_injective Yn Y hYnrun hYrun Yn Y
              (Or.inl (Proofs.NamedAncestry.named_self Yn))
              (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase, Proofs.NamedWire.erase_root]
          subst Yn
          refine ⟨Y.erase, hYprocessed, ?_, ?_⟩
          · rw [← hCnerase]
            exact hCY
          · rw [hview Y hYnbody, hYheight, heq]
    obtain ⟨Y, hYb, hCY, hYh⟩ := hwitness
    have hslot : (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
        (M.vote_time S.E (s + 1))).core.s = s + 1 := by
      rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
    rw [hslot] at hTu
    exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E _ (s + 1) P hP hCmem
      (by rw [facts.hd.setClock_core_F]; exact hFC) hYb hCY
      (by rw [facts.hd.setClock_core_h_max, facts.hd.Sts_setClock_core_σ]; exact hYh)
      (by rw [hrootEq]; exact hroot) Tu hTu
  · exact Or.inr hroot

/-- Under the premises of `fgRoot_preceq_previousHead_through_confirmation_after_GSTOn`, with `s`
    after the deadline's opening slot, `vote_time (s + 1)` in the horizon, `u` in the set for
    `vote_time (s + 1)` and `v` in the set for `vote_time s`: a block `C` that is an ancestor of a
    head `v`'s vote-duty read of slot `s` along `W` can return and is in an outcome of the processed
    tree of a node state of `u`'s vote-duty read of slot `s + 1` along `W` is, for every outcome
    `Tu` of the candidate tree of that node state, in `Tu` or an ancestor of that node state's FG
    root. -/
theorem honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_namedOn
    (facts : Record.Facts M)
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
    {s : Slot}
    (hs : M.opening_slot S.hc (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hhor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    {u v : V} (hu : u ∈ Hs (M.vote_time S.E (s + 1)))
    (hv : v ∈ Hs (M.vote_time S.E s)) {C : Block V}
    {cc : M.Cache}
    (hcc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s)
      (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cc)
    {Tr : Finset (Block V)}
    (hTr : M.voter_filtered_block_tree S.E
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ Tr)
    {L : Finset (GoldfishVote V)}
    (hL : M.voter_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L)
    {L' : Finset (GoldfishVote V)}
    (hL' : M.voter_support_view S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core).toFG.toSG.toGoldfishStore
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s ⇢ L')
    {H : Block V}
    (hH : M.get_head_in_tree_with_layer
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).cache) S.E S.hc
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core) Tr L L'
      ((M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) v).record cc).st.core.s - 1) ⇢ H)
    (hC : Block.Preceq C H)
    {cu : M.Cache}
    (hcu : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).cache ⇢ cu)
    {P : Finset (Block V)}
    (hP : M.voter_processed_block_tree S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record
        cu).st.core).toFG.toSG.toGoldfishStore (s + 1) ⇢ P)
    (hCmem : C ∈ P)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ Tu : Finset (Block V),
      M.voter_filtered_block_tree S.E
        (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu).st.core
        (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record cu).st.core.s ⇢ Tu →
      C ∈ Tu ∨
        Block.Preceq C
          (M.get_fg_root (M.toHealing (M.mkNode
            (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).st
              (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) u).record
            cu).st.core).toFG) := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  have hdeadlineHor :
      (Restated.Vocabulary.Execution.Setup.a M S
        (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ rho.horizon :=
    ((Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S _).le.trans
      (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_succ hs))).trans hhor
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost hdeadlineHor
      hlo hloOpen ht₀ hA
  exact
    Restated.NamedHeightRegimeBaseRunOn.voterCandidateMem_or_preceq_root_of_honestPreviousHead_named
      facts hf hHs hHsXb hX hXXb hcom hbelow
      (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
      hbase hfirst hs hhor hu hv hcc hTr hL hL' hH hC hcu hP hCmem
      (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

end

end DecoupledConsensusModel.Sts.Restated
