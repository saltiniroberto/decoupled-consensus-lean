import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bInvariantActive

/-!
# The honest active attesters of a round

The honest active attesters `HonRound` of a round and the largest `Σ.h_max` they hold, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The honest active attesters of round `r`: the validators the awake rule lets attest at round `r`
    (awake at every time from one delay before round `r`'s grade-2 first cutoff to round `r`'s action
    instant) that the adversary does not hold at that instant. -/
def HonRound (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Round) : Finset V :=
  Restated.attestersAt M S Sched r \ Sched.adv ((M.a S.hc S.E.Δ r))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The largest `Σ.h_max` held after `n` steps by an honest active attester of round `r` (a member
    of `HonRound` for round `r`). -/
noncomputable def hmaxRoundAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (n : Nat) : Height :=
  (Restated.HonRound M S Sched r).sup fun v => (x[n][v].st).st.core.h_max

end

end DecoupledConsensusModel.Sts.Restated
