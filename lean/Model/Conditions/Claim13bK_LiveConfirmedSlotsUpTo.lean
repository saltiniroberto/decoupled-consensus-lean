import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_LiveConfirmedSlotsUpTo

/-!
# An eligible descendant of the anchor stays an ancestor of the honest heads, up to a slot

The condition `EligibleDescendantOfAnchorPersistsTo`, over the slots up to `sEnd`, stated over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- For every round `r` from the switch round on with anchor `T` (`T_W` or a descendant of it) at
    which the joint invariant holds, every slot `s` from `o_rW + 2` on and between `o_r + 1` and
    `o_{r+1}`, every tick step `m` at slot `s`'s confirmation time, every validator `v` awake from
    one delay before slot `s`'s start to that time and honest through it, and every block `H` that
    some outcome of slot `s`'s eligibility test on `v`'s store after `m` steps passes: if `T` is an
    ancestor of `H`, then every honest active member of the committee of every slot from `s + 1` to
    `sEnd` votes there for a descendant of `H`. -/
def EligibleDescendantOfAnchorPersistsTo (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (n_W : Nat) (T_W : NamedBlock V)
    (sEnd : Slot) : Prop :=
  ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
    Block.Preceq T_W.erase T.erase →
    Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
    ∀ s : Slot, (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s →
      (M.opening_slot S.hc r) + 1 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
    ∀ m : Nat, Restated.tickStepAt M x m (M.confirmation_time S.E s) →
    ∀ v : V, v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
        (M.confirmation_time S.E s) →
      HonestThroughTime Sched (M.confirmation_time S.E s) v →
    ∀ H : Block V, ∀ el : Block V → Bool,
      Restated.Vocabulary.Protocol.confEligible M S.E (x[m][v].st).st.core s ⇢ el → el H = true →
      Block.Preceq T.erase H →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x H (s + 1) sEnd

end

end DecoupledConsensusModel.Sts.Restated
