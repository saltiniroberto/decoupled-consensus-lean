import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.RunAll
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Previous-round SG blocks and the opening-slot votes

The condition that the round-`(rW − 1)` SG blocks are ancestors of the votes of the switch round's
opening slot, stated over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every validator `u` not held at the previous round's action instant that emits along `W` its
    round-`(rW − 1)` attestation from its action read `n u`, every SG block computed from `n u` is
    an ancestor of every vote, emitted along `W`, of the switch round's opening slot cast by a
    committee member not held at that slot's vote instant. -/
def BasePreviousRoundSGBelowOpeningVotes (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (tE : Int) (N : Nat)
    (W : Nat → V → M.N) (n : V → M.N) : Prop :=
  ∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))),
    ∀ D : M.NS × M.NR × NamedAttestation V,
      M.duties_attest_with (M.gradeContract (n u).cache)
          (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node u)
          (n u).st (n u).record ⇢ D →
    Restated.Vocabulary.Execution.Run.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) W u
        (Object.attest D.2.2)
        ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) →
      (let gc := M.gradeContract (n u).cache
       let st := M.toHealing (n u).st.core
       let k := M.round_of (Setup.alwaysAwake S).hc st.s
       ∀ A2 : Option (Block V),
         M.grade2_block_with gc (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc st k ⇢ A2 →
       ∀ G : Block V,
         M.get_sg_vote_with gc (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc st k A2 ⇢ G →
       Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) W
        (notHeldAt Sched) Finset.univ ((M.opening_slot S.hc (Restated.switchRound M S tE)))
        (fun X => Block.Preceq G X))

end

end DecoupledConsensusModel.Sts.Restated
