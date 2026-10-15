module
public import Proofs.Vocabulary.Protocol.Grades.LifecycleActionSource
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.ProposalRows_inWindow
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.Protocol.ChainState.HeightProgressFixedRootRows
public import Proofs.Vocabulary.Generic.FixedHeightRootAdmission
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import Proofs.Vocabulary.Protocol.Grades.RecoveryCapturedSlotInterval
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
import Proofs.Vocabulary.Protocol.Handlers.Proposer
import Proofs.Vocabulary.Protocol.Grades.CleanReadBridge
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalWalkTransportCore
import Proofs.Vocabulary.Protocol.Grades.HeightProgressClosureBatchAlignedSite
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressLadder
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


omit [Fintype V] in
private theorem fixedRootNamedParent_preceq_of_parent?
    {B P : NamedBlock V} (h : NamedBlock.parent? B = some P) :
    NamedBlock.Preceq P B := by
  cases B with
  | genesis => cases h
  | node parent slot root votes support rows proposer =>
      have hparent : parent = P := Option.some.inj h
      subst P
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)


omit [Fintype V] in
private theorem fixedRootMem_named_chain_attestations_own
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)


omit [Fintype V] in
private theorem fixedRootFresh_parent_preceq_self (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

omit [DecidableEq V] [Fintype V] in
private theorem fixedRootFresh_heightCases_nat {a m : Nat} (hlo : m - 1 ≤ a)
    (hhi : a ≤ m) : a = m - 1 ∨ a = m := by
  omega


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
