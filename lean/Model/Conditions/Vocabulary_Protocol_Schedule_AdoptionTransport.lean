import Proofs.Vocabulary.Protocol.Schedule.AdoptionTransport
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Acceptance window of the confirmation votes

The condition that every confirmation vote of a slot was accepted inside that slot's voting window,
stated over a model `M : Record.Model V` along a path `W` of the run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- For every outcome `X` of `source`'s confirmation votes of slot `s`, every Goldfish vote `u` of
    `X` has slot `s` and is accepted by `v` at some event of `rho`, read along the path `W`, at a
    time `t` with `M.proposal_time S.E s ≤ t < M.support_cutoff S.E s`. -/
def Vocabulary.Protocol.ConfirmationVotesAcceptedInWindow (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (v : V)
    (source : M.S) (s : Slot) : Prop :=
  ∀ X, Restated.Vocabulary.Protocol.confVotes M S.E source s ⇢ X → ∀ u ∈ X,
    ∃ (i : Nat) (t : Time), Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.gfVote u) t ∧
      u.slot = s ∧ M.proposal_time S.E s ≤ t ∧
      t < M.support_cutoff S.E s

end

end DecoupledConsensusModel.Sts.Restated
