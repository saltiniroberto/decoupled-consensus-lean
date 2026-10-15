import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_74

/-!
# Conditions on the SG blocks of the switch round

The conditions on the round-`rW` and round-`(rW − 1)` SG blocks of the validators not held, used at
the switch round, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path of the run that the execution `x` follows, any two validators not held at
    `S.a rW` have compatible round-`rW` SG blocks, read from their node states in that path's world
    before `S.a rW`. -/
def BaseSGOneChainAtSwitchRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (tE : Int) (N : Nat) : Prop :=
  ∀ u ∈ notHeldAt Sched
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)),
    ∀ w ∈ notHeldAt Sched
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)),
    ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)))
        u)
      (Restated.switchRound M S tE),
    ∀ gu : Option (Block V), M.grade2_block_with (M.gradeContract nu.cache)
        (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing nu.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing nu.st.core).s) ⇢ gu →
    ∀ A : Block V, M.get_sg_vote_with (M.gradeContract nu.cache)
        (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing nu.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing nu.st.core).s) gu ⇢ A →
    ∀ nw ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)))
        w)
      (Restated.switchRound M S tE),
    ∀ gw : Option (Block V), M.grade2_block_with (M.gradeContract nw.cache)
        (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing nw.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing nw.st.core).s) ⇢ gw →
    ∀ A' : Block V, M.get_sg_vote_with (M.gradeContract nw.cache)
        (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc (M.toHealing nw.st.core)
        (M.round_of (Setup.alwaysAwake S).hc (M.toHealing nw.st.core).s) gw ⇢ A' →
      A.compatible A' = true

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Every validator not held at `S.a (rW − 1)` that emits along the path `W` its round-`(rW − 1)`
    attestation has its SG block, read from its node state in the world of `W` before
    `S.a (rW − 1)`, on one chain with `T`'s erasure. -/
def BasePreviousRoundSGCompatibleWithAnchor (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (tE : Int) (N : Nat) (W : Nat → V → M.N)
    (T : NamedBlock V) : Prop :=
  Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) W
    (fun t => W (strictEventIndex
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
    (notHeldAt Sched) (Restated.switchRound M S tE - 1) T.erase

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- At a round `r`, every validator not held at `S.a (r − 1)` that emits along the path `W` its
    round-`(r − 1)` attestation has its SG block, read from its node state in the world of `W`
    before `S.a (r − 1)`, on one chain with `T`'s erasure. -/
def BasePreviousRoundSGCompatibleWithAnchorAtRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (r : Round) (N : Nat) (W : Nat → V → M.N)
    (T : NamedBlock V) : Prop :=
  Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) W
    (fun t => W (strictEventIndex
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
    (notHeldAt Sched) (r - 1) T.erase

end

end DecoupledConsensusModel.Sts.Restated
