module
public import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Self-acceptance of an honest proposal -/


/-- An honest proposer's tick at slot `s`'s proposal time is an accepting event of its proposed
    block `B`. -/
theorem acceptsAt_proposedBlock_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    ∃ i : Nat, NamedRun.acceptsAt S rho i (S.E.proposer s)
      (.block B) (Protocol.proposal_time S.E s) := by
  obtain ⟨B0, hB0, -, i₁, hi₁, hemem⟩ :=
    DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_emits_of_honest S
      adm.toNamedScheduleWellFormed s hs hprop hhor
  have hBeq : B0 = B := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_unique S rho s hB0 hB
  subst hBeq
  have hadmit := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_admit S adm s hs hB
  obtain ⟨i₂, hi₂, hmem⟩ :=
    DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_mem_bodies_after_tick S
      adm.toNamedScheduleWellFormed s hs hprop hhor hB hadmit
  have hij : i₁ = i₂ :=
    Proofs.HealingSurface.index_unique_of_nodup adm.toNamedScheduleWellFormed.nodup hi₁ hi₂
  subst hij
  refine ⟨i₁, ⟨Or.inl ⟨Protocol.proposal_time S.E s, hi₁, hemem⟩,
      ⟨Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s),
        hi₁, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [NamedReceipt.processed, decide_eq_false_iff_not]
    have hstateEq : NamedRun.stateBefore S rho i₁ (S.E.proposer s) =
        NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s) :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S adm.toNamedScheduleWellFormed hi₁
    rw [hstateEq]
    intro hmemB
    have htree : (Statements.Instantiation.proposerReadAt S rho s).st.core.T =
        (Statements.Instantiation.proposerReadAt S rho s).st.bodies.image NamedBlock.erase :=
      (DecoupledConsensusModel.Proofs.HealingSurface.proposerReadAt_invariant S rho s).1.1
    exact Proofs.HealingSurface.proposedBlockErased_fresh_at_tick S adm s hs hB
      (htree ▸ Finset.mem_image_of_mem NamedBlock.erase hmemB)
  · simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hmem


end Protocol
end DecoupledConsensusModel

end
