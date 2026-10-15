import Proofs.Vocabulary.Protocol.Store.RawSource
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Record.Wiring

/-!
# Rows sit in the bucket of their round

In every world of a run, a named row in bucket `k` of a store's rows is a row of round `k`, stated
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRawSource
open Execution DecoupledConsensusModel.Protocol

/-- For every world `w₁` before the `i`-th event of `rho`, if the named row `a` is in bucket `k` of
    the rows of `reader`'s store in `w₁`, then `a` is a row of round `k`. -/
theorem Vocabulary.Proofs.NamedRawSource.row_round_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (reader : V)
    (k : Round) (a : NamedAttestation V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, a ∈ (w₁ reader).st.sg_rows k → a.round = k :=
  facts.stoRun.row_round_stateBefore S rho i reader k a

end

end DecoupledConsensusModel.Sts.Restated
