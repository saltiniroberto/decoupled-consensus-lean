module
public import Proofs.Vocabulary.Execution.PrefixThroughHistory
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights
public import Proofs.Vocabulary.Protocol.Handlers.NamedStore
import Proofs.Vocabulary.Objects.Weights
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistoryTime
open Execution Protocol
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
theorem ancestor_body_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent






end DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistoryTime

end
