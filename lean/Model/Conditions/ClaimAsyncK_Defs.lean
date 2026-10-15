import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_Defs

/-!
# The long-term condition and classified votes

The long-term condition read at one instant, and the classification of the height votes of the sent
log against a block, stated over a model `M : Record.Model V`.
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

/-- Three times the weight of `activeOutsideFixedIn S Sched r` together with the adversary's set at
    `tEnd` is less than twice the total weight. -/
def longTermConditionUpToW (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) (tEnd : Int) : Prop :=
  3 * S.E.electorate.weightOf (Restated.activeOutsideFixedIn M S Sched r ∪ Sched.adv tEnd)
    < 2 * S.E.electorate.totalWeight

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every height vote in the sent log `x[k].sent` whose signer is honest through step `k` is bound
    to a root whose blocks on the wire are ancestors or descendants of `P`, or is for a height less
    than the justified height of every validator honest through step `n₁ + 1`, or is signed by a
    member of `activeOutsideFixedIn S Sched r`. -/
def VotesClassified (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Nat) (P : Block V) (n₁ k : Nat) : Prop :=
  ∀ (u : V) (a : NamedAttestation V) (h : Height) (root : BlockId) (tmo : Bool),
    Restated.HonestThrough M Sched x k u → a.val_index = u →
    (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent →
    a.height_pair = NamedHeightPair.vote h root tmo →
    (∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
        Block.Compatible P C.erase) ∨
      (∀ w : V, Restated.HonestThrough M Sched x (n₁ + 1) w → h < (x[n₁ + 1][w].st).st.core.h_j) ∨
      u ∈ Restated.activeOutsideFixedIn M S Sched r

end

end DecoupledConsensusModel.Sts.Restated
