import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.RunAll
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Planned opening rows

The condition that every validator not held at a round's action instant votes the height of a block
`P` with `P`'s entry as target, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Along the path of the run named by `v₀` and `N` that `x` follows, every validator `v₁` not held
    at `S.a q` has every round-`q` attestation its attestation duty can return carrying the height
    pair `vote h(P) T_h(P) b` for some bit `b`, with `b = false` when `nj(P) = false`. -/
def OpeningRowsPlanned (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (N : Nat) (q : Round) (P : NamedBlock V) : Prop :=
  ∀ v₁ ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v₀ N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) } :
            Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q))
        v₁) q,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) (Setup.alwaysAwake S).E
        (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v₁) n.st n.record ⇢ D →
    (D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root true) ∧
      ((M.derive_named S.E S.cfg P).nj = false →
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false)

end

end DecoupledConsensusModel.Sts.Restated
