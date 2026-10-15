import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# Finalized blocks and the anchor

Conditions relating the finalized blocks of honest validators to an anchor block `T₀`, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every step `n' ≤ n₀ + 1`, the block finalized by a validator honest through `n'` lies on one
    chain with `T₀`. -/
def BaseFinalizedCompatibleWithAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n₀ : Nat) (T₀ : NamedBlock V) : Prop :=
  ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
    Block.compatible (x[n'][v].st).st.core.F T₀.erase = true

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every step `n' ≤ n₀ + 1`, the chain-state height that a validator honest through `n'` records
    for its own finalized block is at most the chain-state height of `T₀`. -/
def BaseRecordedFinalizedHeightUnderAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (n₀ : Nat) (T₀ : NamedBlock V) : Prop :=
  ∀ (v : V) (n' : Nat), n' ≤ n₀ + 1 → Restated.HonestThrough M Sched x n' v →
    ((x[n'][v].st).st.core.σ (x[n'][v].st).st.core.F).h
      ≤ (M.derive_named S.E S.cfg T₀).h

end

end DecoupledConsensusModel.Sts.Restated
