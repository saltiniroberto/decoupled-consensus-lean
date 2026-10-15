module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads
import Proofs.Vocabulary.Execution.BodyRetention
import Proofs.Vocabulary.Execution.Runtime
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] [DecidableEq V] in
/-- A finality pair `finality_pair Λ h_j J h_F` has height `h_j`. -/
theorem finality_pair_height {Λ : Record} {h_j : Height} {J : BlockId}
    {h_F h : Height} {T : BlockId}
    (hp : Protocol.finality_pair Λ h_j J h_F = some ⟨h, T⟩) : h_j = h := by
  simp only [Protocol.finality_pair] at hp
  split_ifs at hp
  simp_all

/-- The named round action's finality pair is `finality_pair` at the round action's Goldfish head. -/
theorem round_action_finality_pair (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    ∃ Hd : Block V,
      Hd = Protocol.get_head_with contract E hc st (st.pool st.s)
        ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s ∧
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
        Protocol.finality_pair record.legacy
          (st.σ Hd).h_j (st.σ Hd).J.root (st.σ Hd).h_F :=
  ⟨_, rfl, rfl⟩

theorem round_action_head_mem_frame
    (cache : DecoupledConsensusModel.Protocol.Cache V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : Protocol.Store V) (record : Protocol.NamedRecord)
    (hJ : st.J ∈ st.T) (hF : st.F ∈ st.T)
    {h : Height} {T : BlockId}
    (hp : (Protocol.NamedActions.round_action_with
        (DecoupledConsensusModel.Protocol.frameContract cache) E hc nd st.toHealing record).2.finality_pair =
      some ⟨h, T⟩) :
    ∃ Hd ∈ st.T, (st.σ Hd).h_j = h := by
  obtain ⟨Hd, hHd, heq⟩ :=
    round_action_finality_pair (DecoupledConsensusModel.Protocol.frameContract cache) E hc nd
      st.toHealing record
  have hp' : Protocol.finality_pair record.legacy (st.toHealing.σ Hd).h_j
      (st.toHealing.σ Hd).J.root (st.toHealing.σ Hd).h_F = some ⟨h, T⟩ := by
    rw [← heq]
    exact hp
  refine ⟨Hd, ?_, finality_pair_height hp'⟩
  rw [hHd]
  apply NamedProposalParent.runtime_get_head_mem cache E hc st.toHealing _ _ _
  change (if st.h_max = st.h_j + 1 then st.J else st.F) ∈ st.T
  split_ifs <;> assumption


end Proofs
end DecoupledConsensusModel

end
