import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_42

/-!
# Proposer recurrence and the blocks of a run

The conditions `ProposerCarrierAtOn` and `MultiProposerRecurrenceOn` on the proposers of a round's
first slots, and the blocks of a run read through a set of validators along a path of worlds, stated
over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The proposer of each of round `r`'s first three slots is in the set `Hs` gives for that slot's
    confirmation time. -/
def ProposerCarrierAtOn (M : Record.Model V) (S : Setup V) (Hs : Int → Finset V) (r : Round) : Prop :=
  ∀ k : Nat, k < 3 → S.E.proposer ((M.opening_slot S.hc r) + k) ∈
    Hs (M.confirmation_time S.E ((M.opening_slot S.hc r) + k))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every round `r` whose opening slot's proposal time is at least `t₀` and whose window of
    `gap` rounds ends by `tEnd`, some round `r'` from `r` to `r + gap` satisfies
    `ProposerCarrierAtOn`. -/
def MultiProposerRecurrenceOn (M : Record.Model V) (S : Setup V) (Hs : Int → Finset V) (gap : Nat)
    (t₀ tEnd : Int) : Prop :=
  ∀ r : Round, t₀ ≤ M.proposal_time S.E ((M.opening_slot S.hc r)) →
    M.proposal_time S.E ((M.opening_slot S.hc r)) + (gap : Int) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) ≤ tEnd →
    ∃ r' : Round, r ≤ r' ∧ r' ≤ r + gap ∧ Restated.ProposerCarrierAtOn M S Hs r'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `B` is delivered as an object in `rho`, or for some member `v` of `Xb` and some index `i`, the
    world `W i` of the path `W` has `B` among `v`'s bodies. -/
def directBlockInRunOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Xb : Finset V) (B : NamedBlock V) : Prop :=
  NamedObject.block B ∈ Restated.objects rho ∨
    ∃ v ∈ Xb, ∃ i : Nat, B ∈ (W i v).st.bodies

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `A` is an ancestor of a block that satisfies `directBlockInRunOn` along the path `W`. -/
def blockInRunOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Xb : Finset V) (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, Restated.directBlockInRunOn M S rho W Xb B ∧ A.Preceq B

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `A` is a block of the run `rho` read through the stores of `Xb` along the path `W`, that is,
    `blockInRunOn`. -/
def RunBlockOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Xb : Finset V) (A : NamedBlock V) : Prop :=
  Restated.blockInRunOn M S rho W Xb A

end

/-! ## Agreement at the model `Record.Model.vocabulary` -/

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `_root_.DecoupledConsensusModel.Sts.ProposerCarrierAtOn` holds exactly when
    `Restated.ProposerCarrierAtOn` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem ProposerCarrierAtOn_vocabulary_eq (S : Setup V) (Hs : Int → Finset V) (r : Round) :
    _root_.DecoupledConsensusModel.Sts.ProposerCarrierAtOn (V := V) S Hs r ↔ Restated.ProposerCarrierAtOn (V := V) Record.Model.vocabulary S Hs r :=
  Iff.rfl

/-- `_root_.DecoupledConsensusModel.Sts.MultiProposerRecurrenceOn` holds exactly when
    `Restated.MultiProposerRecurrenceOn` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem MultiProposerRecurrenceOn_vocabulary_eq (S : Setup V) (Hs : Int → Finset V) (gap : Nat) (t₀ tEnd : Int) :
    _root_.DecoupledConsensusModel.Sts.MultiProposerRecurrenceOn (V := V) S Hs gap t₀ tEnd ↔ Restated.MultiProposerRecurrenceOn (V := V) Record.Model.vocabulary S Hs gap t₀ tEnd :=
  Iff.rfl

/-- `_root_.DecoupledConsensusModel.Sts.directBlockInRunOn` holds exactly when
    `Restated.directBlockInRunOn` holds at the model `Record.Model.vocabulary` along the path
    `fun i => NamedRun.stateBefore S rho i`. -/
@[record_vocabulary]
theorem directBlockInRunOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (B : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.directBlockInRunOn (V := V) S rho Xb B ↔
      Restated.directBlockInRunOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) Xb B := by
  unfold Restated.directBlockInRunOn
  rw [Restated.objects_ofVocabulary]
  exact Iff.rfl

/-- `_root_.DecoupledConsensusModel.Sts.blockInRunOn` holds exactly when `Restated.blockInRunOn`
    holds at the model `Record.Model.vocabulary` along the path
    `fun i => NamedRun.stateBefore S rho i`. -/
@[record_vocabulary]
theorem blockInRunOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (A : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.blockInRunOn (V := V) S rho Xb A ↔
      Restated.blockInRunOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) Xb A :=
  exists_congr fun B => and_congr_left fun _ => directBlockInRunOn_vocabulary_eq S rho Xb B

/-- `_root_.DecoupledConsensusModel.Sts.RunBlockOn` holds exactly when `Restated.RunBlockOn` holds
    at the model `Record.Model.vocabulary` along the path `fun i => NamedRun.stateBefore S rho i`. -/
@[record_vocabulary]
theorem RunBlockOn_vocabulary_eq (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (A : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.RunBlockOn (V := V) S rho Xb A ↔
      Restated.RunBlockOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) Xb A :=
  blockInRunOn_vocabulary_eq S rho Xb A

end

end DecoupledConsensusModel.Sts.Restated
