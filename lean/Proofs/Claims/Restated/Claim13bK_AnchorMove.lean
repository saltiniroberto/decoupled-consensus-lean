import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bStepSGMove
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The next round's anchor lies on one chain with a block

Over a model `M : Record.Model V`: when the confirmed blocks and grade-2 candidates of the honest
attesters' round-`(r + 1)` action reads lie on one chain with `T`, so does the round-`(r + 1)`
anchor (`newAnchor_compatible_old_ofSpec`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` and `k a` can return `b`. -/
private theorem returns_bind_iff_anchorMove {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
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

/-- The finality-gadget source at every node state `n` can return some value. -/
private theorem actionFGSource_nonempty_anchorMove (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff_anchorMove _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- If every healing store of the round-`r₁` action read from `before` has its confirmed block on
    one chain with `B`, and every grade-2 result of that read that is a block is on one chain with
    `B`, then every block the finality-gadget source can return at a node state of the read is on
    one chain with `B`. -/
private theorem source_compatible_anchorMove (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r₁ : Round) (B : Block V)
    (hconf : ∀ hs ∈ Restated.actionHealingStore M S before r₁,
      Block.compatible (hs : M.HS).live_confirmed B = true)
    (hg2 : ∀ f ∈ Restated.actionFrame M S before r₁, ∀ root : Block V,
      (f : M.Frame).g2 = some (some root) → Block.compatible root B = true)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r₁)
    (Cfg : Block V)
    (hCfg : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) n ⇢
      some Cfg) :
    Block.compatible Cfg B = true := by
  rcases Restated.source_cases facts S before r₁ n hn Cfg hCfg with hlc | hQ
  · exact Protocol.compatible_of_preceq_of_compatible hlc (hconf _ ⟨n, hn, rfl⟩)
  · obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) r₁
    have hgQ : g.Q2 = some Cfg := hQ g ((facts.nd.gradeContract_read _ _ _ _ _ _).1 hg)
    obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
      (M.readFrame n.cache (M.toHealing n.st.core) r₁)
    have hgo : g.Q2 = o :=
      facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc (M.toHealing n.st.core) r₁
        g hg o ho
    exact facts.gr.Q2_compatible (hg2 _ ⟨n, hn, rfl⟩) o ho (by rw [← hgo, hgQ])

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n'` is the tick at round `r + 1`'s action instant, then for every choice `att` of the
    round-`(r + 1)` action attestations: if every validator honest through step `n' + 1` and awake
    throughout the `wAttest S` window before that instant has, at every node state of its
    round-`(r + 1)` action read, a confirmed block and a grade-2 candidate on one chain with `T`,
    then `T` and the round-`(r + 1)` anchor along `att` lie on one chain. -/
theorem newAnchor_compatible_old_ofSpec (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    {T : NamedBlock V}
    (hconf : ∀ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1),
        Block.compatible (hs : M.HS).live_confirmed T.erase = true)
    (hg2 : ∀ q ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][q].st) (r + 1), ∀ root : Block V,
        (f : M.Frame).g2 = some (some root) → Block.compatible root T.erase = true) :
    Block.compatible T.erase (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  classical
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
        else T) = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    -- the node state of the action read `att q` was computed from
    obtain ⟨n, hn, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := actionFGSource_nonempty_anchorMove facts (Setup.alwaysAwake S) n
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl n hn
        (ns, rec, att q) hD hvote o ho
    rw [hchoice]
    exact Protocol.compatible_comm
      (Protocol.compatible_of_preceq_of_compatible hpre
        (source_compatible_anchorMove facts S (x[n'][q].st) (r + 1) T.erase (hconf q hqW)
          (hg2 q hqW) n hn Cfg ho))
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = T := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
        else T) = T
      rw [dif_neg hex]
    rw [hchoice]
    exact Block.compatible_of_preceq_common (Block.preceq_self _) (Block.preceq_self _)

end

end DecoupledConsensusModel.Sts.Restated
