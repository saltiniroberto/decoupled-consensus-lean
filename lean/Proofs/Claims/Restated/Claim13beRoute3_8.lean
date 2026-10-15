import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_8
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The anchor at the switch round's action instant

Theorems over a model `M : Record.Model V` and its facts about an execution `x` and an anchor `T₀`
at the switch round: some step is the tick at the switch round's action instant, the anchor is in
play, it is its own chain-state height's entry, and every block an honest validator has finalized up
to the step after that tick is an ancestor of it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- On an execution whose clock diverges, some step is the tick at the action instant of the switch
    round `switchRound M S tE`. -/
theorem exists_tick_at_switchRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) (tE : Int) :
    ∃ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) :=
  Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (Restated.switchRound M S tE))

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If some validator honest through its own read has the anchor `T₀` among its store's bodies, then
    `T₀` is one of the blocks the execution put in play. -/
theorem inPlay_at_switchRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {T₀ : NamedBlock V}
    (hheld : ∃ (m : Nat) (v : V), Restated.HonestThrough M Sched x m v ∧ T₀ ∈ (x[m][v].st).st.bodies) :
    Restated.blockInLog M S Sched x T₀ := by
  obtain ⟨m, v, hv, hmem⟩ := hheld
  exact Restated.blockInLog_of_mem_bodies facts S Sched hv hmem

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If some validator honest through its own read holds a block in its store's tree whose recorded
    chain state names the erasure of `T₀` as that height's entry, then the replay of `T₀` names `T₀`
    as its chain-state height's entry. -/
theorem anchorEntry_at_switchRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {T₀ : NamedBlock V}
    (hlog : Restated.blockInLog M S Sched x T₀)
    (hentry : ∃ (m : Nat) (v : V), Restated.HonestThrough M Sched x m v ∧
      ∃ Cfg : Block V, Cfg ∈ (x[m][v].st).st.core.T ∧
        ((x[m][v].st).st.core.σ Cfg).T_h = T₀.erase) :
    (M.derive_named S.E S.cfg T₀).T_h = T₀.erase := by
  classical
  obtain ⟨m, v, hv, Cfg, hCfgT, hTh⟩ := hentry
  have hco := (Restated.nodeInvariant_sts facts S Sched x m v).1.1.1
  rw [hco.1] at hCfgT
  obtain ⟨Cfgn, hCfgnMem, hCfgnErase⟩ := Finset.mem_image.mp hCfgT
  have hσ : (x[m][v].st).st.core.σ Cfg = M.derive_named S.E S.cfg Cfgn := by
    have hd := hco.2.2.2.2 Cfgn hCfgnMem
    rw [hCfgnErase] at hd
    exact hd
  obtain ⟨En, hEnLe, hEnEr, hEnH⟩ :=
    facts.cs.entry_ancestor_same_height S.E S.cfg Cfgn
  have hEnSelf : (M.derive_named S.E S.cfg En).T_h = En.erase := by
    rw [facts.cs.entry_eq_on_plateau S.E S.cfg hEnLe hEnH]
    exact hEnEr.symm
  have hEnMem : En ∈ (x[m][v].st).st.bodies :=
    Restated.mem_bodies_of_preceq hco.2.2.1 hCfgnMem hEnLe
  have hEnLog : Restated.blockInLog M S Sched x En := Restated.blockInLog_of_mem_bodies facts S Sched hv hEnMem
  have hEnEr' : En.erase = T₀.erase := by
    rw [hEnEr, ← hσ]
    exact hTh
  have hroot : En.root = T₀.root := by
    rw [← Proofs.NamedWire.erase_root En, hEnEr', Proofs.NamedWire.erase_root T₀]
  have hEnT₀ : En = T₀ :=
    hexec.idealization.root_injective En T₀ hEnLog hlog En T₀
      (Or.inl (Proofs.NamedAncestry.named_self En))
      (Or.inr (Proofs.NamedAncestry.named_self T₀)) hroot
  rw [← hEnT₀, hEnSelf, hEnEr']

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whatever a validator honest through its own read has finalized, at any step up to the step after
    the tick `n₀`, is an ancestor of the anchor `T₀`. -/
theorem fin_at_switchRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {n₀ : Nat} {T₀ : NamedBlock V}
    (hlog : Restated.blockInLog M S Sched x T₀)
    (hcomp : Restated.BaseFinalizedCompatibleWithAnchor M S Sched x n₀ T₀)
    (hheight : Restated.BaseRecordedFinalizedHeightUnderAnchor M S Sched x n₀ T₀) :
    ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
      Block.Preceq (x[n'][v].st).st.core.F T₀.erase := by
  classical
  intro v n' hn' hv
  obtain ⟨D, hDmem, hDF, -⟩ := Restated.finalization_carrier_sts facts S Sched x n' v
  rcases facts.csAdded.finalized_is_entry S.E S.cfg D with hz | ⟨Fn, hFnD, hFnerase, hFnh, hFnself⟩
  · have hgen : (M.derive_named S.E S.cfg D).F = Block.genesis :=
      facts.cs.finalized_zero_is_genesis S.E S.cfg D hz
    rw [← hDF, hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · have hco := (Restated.nodeInvariant_sts facts S Sched x n' v).1.1.1
    have hFnMem : Fn ∈ (x[n'][v].st).st.bodies :=
      Restated.mem_bodies_of_preceq hco.2.2.1 hDmem hFnD
    obtain ⟨Fb, hFbMem, hFbe, hFbσ⟩ := Restated.finalized_body_of_store facts S Sched x n' v
    have hFnFb : Fn = Fb := by
      refine hco.2.1 Fn hFnMem Fb hFbMem ?_
      rw [hFnerase, hDF, ← hFbe]
    have hrec : ((x[n'][v].st).st.core.σ (x[n'][v].st).st.core.F).h
        = (M.derive_named S.E S.cfg Fn).h := by
      rw [hFbσ, hFnFb]
    have hle : (M.derive_named S.E S.cfg Fn).h
        ≤ (M.derive_named S.E S.cfg T₀).h := by
      rw [← hrec]
      exact hheight v n' hn' hv
    have hc : Block.compatible Fn.erase T₀.erase = true := by
      rw [hFnerase, hDF]
      exact hcomp v n' hn' hv
    have hres : Block.Preceq Fn.erase T₀.erase :=
      Restated.preceq_of_entry_compatible_sts facts S Sched x hexec.idealization
        (Restated.blockInLog_of_mem_bodies facts S Sched hv hFnMem) hlog hFnself hc hle
    rw [← hDF, ← hFnerase]
    exact hres

end

end DecoupledConsensusModel.Sts.Restated
