import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Constants
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedConfirmationWalk
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterInterference
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_42c

/-!
# Fixed roots, opening proposals and round ceilings over a model

Conditions on fixed-height justification roots, opening proposals and their lifecycles, round
ceilings and height-progress seeds of a run, stated over a model `M : Record.Model V` and read along
a path `W` of the run or in the worlds before each instant. The last section proves that each
agrees, at the model `Record.Model.vocabulary`, with the definition of the same name in
`DecoupledConsensusModel.Sts`.
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
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The store `st` has `h_max = H` and `h_max = h_j + 1`, its justified target is the one certified
    target at height `H − 1`, and that target is a run block read through `Xb` along the path `W`. -/
structure FixedHeightJustificationRootOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V)
    (st : M.S) (H : Height) : Prop where
  frontier : st.h_max = H
  justificationHeight : st.h_j = H - 1
  gate : st.h_max = st.h_j + 1
  certificate : Restated.CertificateOn M S rho W Xb (H - 1) st.J.root
  uniqueAtHeight : ∀ T : BlockId, Restated.CertificateOn M S rho W Xb (H - 1) T → T = st.J.root
  targetBlock : Restated.RunBlockOfOn M S rho W Xb st.J

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The store `st` has `h_max = H` and `h_max = h_j + 1`, its justified target is the one certified
    target at height `H − 1`, a run block read through `Xb` along the path `W`, and incompatible
    with `P`. -/
structure FixedHeightRootTargetOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (st : M.S)
    (P : Block V) (H : Height) : Prop where
  frontier : st.h_max = H
  justificationHeight : st.h_j = H - 1
  gate : st.h_max = st.h_j + 1
  certificate : Restated.CertificateOn M S rho W Xb (H - 1) st.J.root
  uniqueAtHeight : ∀ T : BlockId, Restated.CertificateOn M S rho W Xb (H - 1) T → T = st.J.root
  targetBlock : Restated.RunBlockOfOn M S rho W Xb st.J
  incompatible : st.J.compatible P = false

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `w` is in `Hs read`, `read` is within the horizon, and `w`'s store in the world `wd` holds a run
    block (along `W`) carrying its justification and is a fixed-height justification root at `H`
    read through `Xb`. -/
structure FixedHeightJustificationRootAtReadOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (H : Height) (w : V) (read : Time) (wd : V → M.N) : Prop where
  readerHonest : w ∈ Hs read
  readInHorizon : read ≤ rho.horizon
  carrierExists : ∃ D ∈ (wd w).st.bodies, Restated.RunBlockOn M S rho W Xb D ∧
    Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg D (wd w).st.J (wd w).st.h_j
  targetHeightPositive : 0 < H - 1
  fixedTarget : Restated.FixedHeightJustificationRootOn M S rho W Xb (wd w).st.core H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `w` is in `Hs read`, `read` is within the horizon, `w`'s store in the world `wd` holds a run
    block carrying its justification and is a fixed-height justification root at `H`, and `P` is a
    run block of height at least `H` in that store's tree that its finality root interferes with. -/
structure FixedHeightRootInterferenceAtReadOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (H : Height) (w : V) (read : Time) (wd : V → M.N) (P : Block V) : Prop where
  readerHonest : w ∈ Hs read
  readInHorizon : read ≤ rho.horizon
  protectedProcessed : P ∈ (wd w).st.T
  protectedHeight : ∃ Pn : NamedBlock V, Pn.erase = P ∧ Restated.RunBlockOn M S rho W Xb Pn ∧
    H ≤ (M.derive_named S.E S.cfg Pn).h
  interference : Restated.Vocabulary.Proofs.HealingSurface.FGRootInterferenceAt M (wd w).st P
  carrierExists : ∃ D ∈ (wd w).st.bodies, Restated.RunBlockOn M S rho W Xb D ∧
    Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg D (wd w).st.J (wd w).st.h_j
  targetHeightPositive : 0 < H - 1
  fixedTarget : Restated.FixedHeightRootTargetOn M S rho W Xb (wd w).st.core P H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `holder` is in `Hs t`, holds `carrier` in the tree of its store in the world `wd`, and `carrier`
    erases a run block (read through `Xb` along `W`) at height `H`. -/
structure HonestHMaxCarrierAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (t : Time) (wd : V → M.N) (H : Height) (holder : V) (carrier : Block V) : Prop where
  holderHonest : holder ∈ Hs t
  processed : carrier ∈ (wd holder).st.T
  namedWitness : ∃ D : NamedBlock V, D.erase = carrier ∧ Restated.RunBlockOn M S rho W Xb D ∧
    (M.derive_named S.E S.cfg D).h = H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `target` erases the justified block of `fixed`, is a run block read through `Xb` along `W` at
    height `H − 1`, and is the finality root of `pre`, which has `h_max = H`. -/
structure FixedRootPreparedTargetDataOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Xb : Finset V) (H : Height)
    (fixed pre : M.NS) (target : NamedBlock V) : Prop where
  targetErase : target.erase = fixed.J
  targetRun : Restated.RunBlockOn M S rho W Xb target
  targetHeight : (M.derive_named S.E S.cfg target).h = H - 1
  targetHeightPositive : 0 < H - 1
  rootAtProposal : M.get_fg_root (M.toHealing pre.core).toFG = target.erase
  hMaxAtProposal : pre.h_max = H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `target` is a run block at height `H − 1` and the finality root of `pre`, which has `h_max = H`;
    `ceiling` is `A` or `actionCeiling`, a descendant of `pre`'s finality root, and the honest votes
    of the slot before round `q`'s opening slot are for its descendants; some round-`(q − 1)` action
    node state of `actionWitness` from the world `wa` can select `actionCeiling`; and every
    round-`(q − 1)` action carrier from `wa` of a member of `Hs (S.a (q − 1))` is an ancestor of
    `ceiling`. -/
structure FixedRootPreparedParentCandidateOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (H : Height) (q : Round) (w : V) (read : Time) (A : Block V)
    (target : NamedBlock V) (ceiling actionCeiling : Block V) (actionWitness : V)
    (fixed pre : M.NS) (source : M.S) (wa : V → M.N) : Prop where
  targetErase : target.erase = fixed.J
  targetRun : Restated.RunBlockOn M S rho W Xb target
  targetHeight : (M.derive_named S.E S.cfg target).h = H - 1
  targetHeightPositive : 0 < H - 1
  actionWitnessHonest : actionWitness ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
  actionCeilingEq : ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (wa actionWitness) (q - 1),
    ∃ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
      M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ actionCeiling
  ceilingUpper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wa v) (q - 1),
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ B : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B → B ⪯ ceiling
  ceilingCone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1) fun X => ceiling ⪯ X
  ceilingRoot : M.get_fg_root (M.toHealing pre.core).toFG ⪯ ceiling
  ceilingChoice : ceiling = A ∨ ceiling = actionCeiling
  anchorFiltered : A ∈ M.get_filtered_block_tree (M.toHealing source).toFG
  rootAtProposal : M.get_fg_root (M.toHealing pre.core).toFG = target.erase
  hMaxAtProposal : pre.h_max = H

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `P` is a run block read through `Xb`, round `r`'s opening proposer can propose `P` at its node
    state staged from `Wt` at its proposal instant, every round-`r` action node state of a member of
    `Hs (S.a r)` in `Wt (S.a r)` has `P`'s block as its live confirmed block, `P`'s block is an
    ancestor of every round-`r` carrier computed from `Wt (S.a r)`, and every member of
    `Hs (domain (r + 1) .g2)` has `P`'s block active, with every outcome of its round-`(r + 1)`
    grade-2 store grade for it `true`, in `Wt (domain (r + 1) .g2)`. -/
structure NamedRawOpeningLifecycleAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (P : NamedBlock V) : Prop where
  roundPositive : 0 < r
  proposal : ∃ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc r))
          (S.E.proposer (M.opening_slot S.hc r))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc r))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc r))
          (S.E.proposer (M.opening_slot S.hc r))).cache ⇢ c ∧
    M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc r)))
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc r))
          (S.E.proposer (M.opening_slot S.hc r))).st
        (M.proposal_time S.E (M.opening_slot S.hc r))) ⇢ some P
  proposerHonest : S.E.proposer ((M.opening_slot S.hc r)) ∈
    Hs (M.confirmation_time S.E ((M.opening_slot S.hc r)))
  proposalInHorizon : M.proposal_time S.E ((M.opening_slot S.hc r)) ≤ rho.horizon
  runBlock : Restated.blockInRunOn M S rho W Xb P
  liveConfirmed : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S r) v) r,
      n.st.core.live_confirmed = P.erase
  actionCover : Restated.ActionCarriersCoverOn M S rho Hs r P.erase
    (Wt (Restated.Vocabulary.Execution.Setup.a M S r))
  gradeNext : ∀ v ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g2),
    P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (Wt (M.domain S.E S.hc (r + 1) Phase.g2) v) ∧
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (Wt (M.domain S.E S.hc (r + 1) Phase.g2) v).st (r + 1) Phase.g2 P.erase ⇢ b → b = true

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The lifecycle of the proposal `P` of slot `s + 1`, the opening slot of round `r + 1`: its
    proposer can propose `P`, the round-`r` action carriers and grade-1 blocks are ancestors of its
    proposed parent, the slot's honest votes name `P`'s block along `W`, each confirmer's
    confirmation, read from the worlds `w₁` and `w₂`, is `P`, every outcome of the G0 clearance test
    for `P`'s block at round `r + 1`'s action node states is `true`, and
    `NamedRawOpeningLifecycleAtOn` holds for `P` at round `r + 1`. -/
structure NamedSGProposalLifecyclePacketOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (w₁ w₂ : V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (s : Slot) (P : NamedBlock V) : Prop where
  openingSlot : s + 1 = (M.opening_slot S.hc (r + 1))
  proposal : ∃ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).cache ⇢ c ∧
    M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))) ⇢ some P
  actionTargetParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S r) v) r,
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ C : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).cache ⇢ c →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
              (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
            (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
            (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st.core) ⇢ I →
      C ⪯ I.parent
  liveG1Parent : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g1), ∀ X : Block V,
    (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (Wt (M.domain S.E S.hc (r + 1) Phase.g1) w).st (r + 1) Phase.g1 X ⇢ b → b = true) →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
          (S.E.proposer (M.opening_slot S.hc (r + 1)))).cache ⇢ c →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc (r + 1))))
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
              (S.E.proposer (M.opening_slot S.hc (r + 1)))).st
            (M.proposal_time S.E (M.opening_slot S.hc (r + 1))))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc (r + 1)))
            (S.E.proposer (M.opening_slot S.hc (r + 1)))).record c).st.core) ⇢ I →
      X ⪯ I.parent
  honestVotes : Restated.NamedHonestVotesNameOn M S rho W Hs ((M.opening_slot S.hc (r + 1))) P.erase
  genuineConfirmation : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))),
    Restated.Vocabulary.Internal.GenuineConfirmationAt M S rho v ((M.opening_slot S.hc (r + 1))) w₁ w₂ ∧
      (w₂ v).st.live_confirmed = P.erase
  g0ClearAtAction : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) v) (r + 1),
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n (r + 1) P.erase ⇢ b →
        b = true
  lifecycle : Restated.NamedRawOpeningLifecycleAtOn M S rho W Wt Hs Xb (r + 1) P

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The inputs about slot `s + 1`, the opening slot of round `r + 1`, its proposal `P` and the
    anchor `A`: timing and horizon conditions, `NamedSGTargetConeCanonicalityOn` and
    `NamedG1ConcentrationOn` at round `r`, an honest proposer whose anchor is `A` with grade 1, the
    round-`r` carriers and grade-1 blocks ancestors of the proposed parent, the frozen votes and
    confirmation node states of slot `s + 1`, and the round-`(r + 1)` action readers' SG roots
    ancestors of `P`'s block. -/
structure NamedSGProposalLifecycleInputsOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (X Xb : Finset V) (r : Round) (s : Slot) (A : Block V) (P : NamedBlock V) : Prop where
  openingSlot : s + 1 = (M.opening_slot S.hc (r + 1))
  proposal : ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho (s + 1), p = some P
  postPreviousAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r)
  postProposalSnapshot : S.E.t_GST ≤ M.proposal_time S.E s
  previousSupportInHorizon : M.support_cutoff S.E s ≤ rho.horizon
  actionInHorizon : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ rho.horizon
  nextCutoffInHorizon : M.domain S.E S.hc (r + 1 + 1) Phase.g2 ≤ rho.horizon
  canonical : Restated.NamedSGTargetConeCanonicalityOn M S rho W Hs Xb r s
    (Wt (Restated.Vocabulary.Execution.Setup.a M S r))
  concentration : Restated.NamedG1ConcentrationOn M S rho W Wt Hs Xb r s
  proposerHonest : S.E.proposer (s + 1) ∈ Hs (M.confirmation_time S.E (s + 1))
  proposalAnchor : ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (s + 1),
    ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (r + 1) ⇢ a → a = A
  proposalAnchorG1 : ∀ n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (s + 1),
    ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc n.st (r + 1) Phase.g1 A ⇢ b →
      b = true
  actionTargetParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
    ∀ C ∈ Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt M S rho v r,
    ∀ Q ∈ Restated.Vocabulary.Proofs.HealingSurface.proposedParent M S rho (s + 1), C ⪯ Q
  liveG1Parent : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g1), ∀ B : Block V,
    (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (Wt (M.domain S.E S.hc (r + 1) Phase.g1) w).st (r + 1) Phase.g1 B ⇢ b → b = true) →
      ∀ Q ∈ Restated.Vocabulary.Proofs.HealingSurface.proposedParent M S rho (s + 1), B ⪯ Q
  frozenVote : ∀ v ∈ Hs (M.vote_time S.E (s + 1)), v ∈ S.E.committee (s + 1) →
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho (s + 1),
    ∀ m ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho v (s + 1),
      Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningFrozenVoteAt M S rho s A v P n m
  confirmationRead : ∀ v ∈ Hs (M.confirmation_time S.E (s + 1)),
    Restated.Vocabulary.Proofs.HealingSurface.NamedSGOpeningConfirmationRead M S rho (s + 1) v P
  actionBatchAligned : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v (r + 1),
    Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt M S.hc (M.gradeView (M.toHealing n.st.core)) n.st.core.F X (r + 1)
      (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc (r + 1)) P.erase
  actionRootPreceq : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v (r + 1),
    ∀ R : Block V,
      M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) (r + 1) ⇢ R →
      R ⪯ P.erase
  nextActive : ∀ v ∈ Hs (M.domain S.E S.hc (r + 1 + 1) Phase.g2),
    ∀ n ∈ Restated.Vocabulary.Internal.PhaseGrades.readAt M S rho (M.domain S.E S.hc (r + 1 + 1) Phase.g2) v,
      P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Round `q`'s opening proposer can propose `P`, the opening slot's honest votes are for
    descendants of `P`'s block along `W`, every confirmer confirms `P`'s block from its node state
    in `Wt` at the confirmation instant, `ActionCarriersCoverOn` holds for `P`'s block at round `q`,
    every member of `Hs (domain (q + 1) .g2)` has `P`'s block active with every outcome of its
    grade-2 store grade `true` in `Wt (domain (q + 1) .g2)`, and `NamedRawOpeningLifecycleAtOn`
    holds for `P` at round `q`. -/
structure GateOffOpeningAdoptionOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (q : Round) (P : NamedBlock V) : Prop where
  proposal : ∃ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c ∧
    M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P
  votes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q)) fun X => P.erase ⪯ X
  genuineConfirmation :
      ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
        ∀ c : M.Cache, M.onPhaseTick S.E S.hc
            (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) v).st.core.toHealing
            (M.confirmation_time S.E ((M.opening_slot S.hc q)))
            (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) v).cache ⇢ c →
        Restated.Vocabulary.Protocol.GenuineConfirmationWith M
          (M.gradeContract
            (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) v).st
                (M.confirmation_time S.E ((M.opening_slot S.hc q))))
              (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) v).record c).cache)
          S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) v).st.core
            (M.confirmation_time S.E ((M.opening_slot S.hc q)))) ((M.opening_slot S.hc q)) P.erase
  actionCover : Restated.ActionCarriersCoverOn M S rho Hs q P.erase
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q))
  gradeNext :
      ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) Phase.g2),
        P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
            (Wt (M.domain S.E S.hc (q + 1) Phase.g2) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
            (Wt (M.domain S.E S.hc (q + 1) Phase.g2) v).st (q + 1) Phase.g2 P.erase ⇢ b → b = true
  lifecycle : Restated.NamedRawOpeningLifecycleAtOn M S rho W Wt Hs Xb q P

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Round `q`'s opening proposer can propose `P`, `P`'s parent has height at least `hM − 1`, timing
    and horizon conditions hold, and in the worlds `Wt` the stores of the opening proposer, the
    opening slot's voters and confirmers, and round `q + 1`'s action readers have `h_max = hM` and
    `h_j + 2 ≤ hM`, all but the proposer's holding `P`'s block. -/
structure NamedGateOffOpeningWindowAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (hM : Height) (q : Round) (P : NamedBlock V) : Prop where
  proposal : ∃ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c ∧
    M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P
  roundPositive : 0 < q
  postPreviousAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1))
  postFrozenSnapshot : S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc q) - 1)
  postOpeningVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc q))
  previousCutoffInHorizon : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ q ≤ rho.horizon
  nextActionInHorizon : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon
  parentHeight : hM - 1 ≤ (M.derive_named S.E S.cfg P.parent).h
  proposerFrontier : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc q))).h_max = hM
  proposerGateOff : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc q))).h_j + 2 ≤ hM
  voteFrontier : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (Wt (M.vote_time S.E (M.opening_slot S.hc q)) v).st.core (M.opening_slot S.hc q)).h_max = hM
  voteGateOff : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (Wt (M.vote_time S.E (M.opening_slot S.hc q)) v).st.core (M.opening_slot S.hc q)).h_j + 2 ≤ hM
  proposalAtVote : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
    P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (Wt (M.vote_time S.E (M.opening_slot S.hc q)) v).st.core (M.opening_slot S.hc q)).T
  confirmationFrontier : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.confirmation_time S.E (M.opening_slot S.hc q)) v).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc q))).h_max = hM
  confirmationGateOff : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.confirmation_time S.E (M.opening_slot S.hc q)) v).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc q))).h_j + 2 ≤ hM
  proposalAtConfirmation : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
    P.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.confirmation_time S.E (M.opening_slot S.hc q)) v).st.core
      (M.confirmation_time S.E (M.opening_slot S.hc q))).T
  nextFrontier : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) v).st.core).h_max = hM
  nextGateOff : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) v).st.core).h_j + 2 ≤ hM
  proposalAtNext : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    P.erase ∈ (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) v).st.core).T

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every round-`(q − 1)` action carrier computed from `Wt (S.a (q − 1))` of a member of
    `Hs (S.a (q − 1))`, and every block that a member of `Hs (domain q .g1)` grades 1 in round `q`
    at its store in `Wt (domain q .g1)`, is an ancestor of the parent of every proposal input of
    round `q`'s opening proposer staged from `Wt` at its proposal instant. -/
structure FixedHeightRootOpeningParentRunOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (q : Round) : Prop where
  actionTargetParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) v) (q - 1),
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ C : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ C →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
              (S.E.proposer (M.opening_slot S.hc q))).st
            (M.proposal_time S.E (M.opening_slot S.hc q)))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      C ⪯ I.parent
  liveG1Parent : ∀ w ∈ Hs (M.domain S.E S.hc q Phase.g1), ∀ B : Block V,
    (∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (Wt (M.domain S.E S.hc q Phase.g1) w).st q Phase.g1 B ⇢ b → b = true) →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc q))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c →
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract c) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc q)))
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
              (S.E.proposer (M.opening_slot S.hc q))).st
            (M.proposal_time S.E (M.opening_slot S.hc q)))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
            (S.E.proposer (M.opening_slot S.hc q))).record c).st.core) ⇢ I →
      B ⪯ I.parent

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Round `q`'s opening proposer, picked by `ProposerCarrierAtOn`, holds at its proposal instant two
    run blocks `source` and `root` at height `H` with the same target root: `source` is graded 2 in
    round `q − 1` and active at round `q`'s action readers but not at the proposer's node state,
    while `root` is the proposer's finality root, active there, a strict descendant of `source`, and
    an ancestor of every proposed parent; the largest `h_max` over `Hs endpoint` in `Wend` is at
    most `H`. -/
structure ActiveExactHeightProposalRootCarrierAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Wend : V → M.N)
    (Hs : Int → Finset V) (Xb : Finset V) (H : Height) (q : Round) (endpoint : Time)
    (source root : NamedBlock V) (c : M.Cache) : Prop where
  proposerCarrier : Restated.ProposerCarrierAtOn M S Hs q
  proposerHonest : S.E.proposer ((M.opening_slot S.hc q)) ∈
    Hs (M.confirmation_time S.E ((M.opening_slot S.hc q)))
  proposalRead_le_action : M.proposal_time S.E ((M.opening_slot S.hc q)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q)
  action_le_endpoint : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint
  endpointInHorizon : endpoint ≤ rho.horizon
  endpointCap : ((Hs endpoint).sup fun v => (Wend v).st.core.h_max) ≤ H
  gradeFormsPrev : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) Phase.g2),
    source.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (Wt (M.domain S.E S.hc (q - 1) Phase.g2) v) ∧
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (Wt (M.domain S.E S.hc (q - 1) Phase.g2) v).st (q - 1) Phase.g2 source.erase ⇢ b → b = true
  sourceActiveAtAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    source.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w).st.core).toFG
  sourceProcessed : source ∈
    (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.bodies
  sourceRunBlock : Restated.RunBlockOn M S rho W Xb source
  sourceExactHeight : (M.derive_named S.E S.cfg source).h = H
  sourceNotActive : source.erase ∉ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
    (M.mkNode
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).record c)
  root_eq : root.erase = M.get_fg_root (M.toHealing
    (M.mkNode
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).record
        c).st.core).toFG
  sourceStrictRoot : source.erase ≺ root.erase
  rootActive : root.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
    (M.mkNode
      (M.ns_setClock S.E
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q)))
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).record c)
  rootProcessed : root ∈
    (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.bodies
  rootRunBlock : Restated.RunBlockOn M S rho W Xb root
  rootExactHeight : (M.derive_named S.E S.cfg root).h = H
  rootExactTarget : (M.derive_named S.E S.cfg root).T_h.root = (M.derive_named S.E S.cfg source).T_h.root
  rootPreceqProposedParent : ∀ I : Protocol.ProposalInput V,
    Restated.Vocabulary.Protocol.proposal_input_with M
      (M.gradeContract
        (M.mkNode
          (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st
            (M.proposal_time S.E (M.opening_slot S.hc q)))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).record
            c).cache)
      S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.toHealing
        (M.mkNode
          (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st
            (M.proposal_time S.E (M.opening_slot S.hc q)))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).record
            c).st.core) ⇢ I →
    root.erase ⪯ I.parent

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- An opening lifecycle of round `origin` for `C` after the healing boundary of `r0`, with
    `start < origin < source ≤ bound`, whose block is graded 2 at round `source`, has height greater
    than the largest `h_max` over `Hs (S.a start)` in `Wi (S.a start)`, is justifiable, and has no
    honest height pair at its height emitted before round `origin`'s action
    (`NoLocalHeightPairBeforeOn`). -/
structure BoundedHeightGradeSourceAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt Wi : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (r0 start bound : Round) (origin source : Round) (C : NamedBlock V) : Prop where
  startLtOrigin : start < origin
  originLtSource : origin < source
  sourceUpper : source ≤ bound
  lifecycle : Restated.NamedRawOpeningLifecycleAtOn M S rho W Wt Hs Xb origin C
  originAfterBoundary : Restated.healingBoundaryTime M S r0 < M.proposal_time S.E ((M.opening_slot S.hc origin))
  grade : Restated.NamedGradeFormsAtOn M S rho Hs source C.erase
    (Wt (M.domain S.E S.hc source Phase.g2))
  sourceAbove : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (Wi (Restated.Vocabulary.Execution.Setup.a M S start) u).st.core.h_max) < (M.derive_named S.E S.cfg C).h
  sourceJustifiable : (M.derive_named S.E S.cfg C).nj = false
  originFresh : Restated.NoLocalHeightPairBeforeOn M S rho Hs (strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S origin)))
    (M.derive_named S.E S.cfg C).h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `lag` is positive, and for every start round from `r0` whose `lag` rounds end within the
    horizon, either `BoundedHeightGradeSourceAtOn` holds for some rounds and block, or the largest
    `h_max` over `Hs` in the worlds `Wi` is less at `S.a start` than at `S.a (start + lag)`. -/
def BoundedHeightGradeOrProgressFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt Wi : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (r0 lag : Round) : Prop :=
  0 < lag ∧ ∀ start : Round, r0 ≤ start → (Restated.Vocabulary.Execution.Setup.a M S (start + lag)) ≤ rho.horizon →
    (∃ (origin : Round) (source : Round) (C : NamedBlock V),
        Restated.BoundedHeightGradeSourceAtOn M S rho W Wt Wi Hs Xb r0 start (start + lag) origin source C) ∨
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
          (Wi (Restated.Vocabulary.Execution.Setup.a M S start) u).st.core.h_max) <
        ((Hs (Restated.Vocabulary.Execution.Setup.a M S (start + lag))).sup fun u =>
          (Wi (Restated.Vocabulary.Execution.Setup.a M S (start + lag)) u).st.core.h_max)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member `w` of `Hs (vote_time (s + 1))` and every outcome of the cache update at its
    node state in `Wt (vote_time (s + 1))`, the node state built from them has the vote inputs of
    the cone at `C`; and for every member `w` of `Hs (confirmation_time s)` and every outcome of the
    cache update at its node state in `Wt (confirmation_time s)`, the node state built from them has
    the confirmation inputs. -/
structure GoldfishConeSlotInputsOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (s : Slot)
    (C : Block V) : Prop where
  vote : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
      (Wt (M.vote_time S.E (s + 1)) w).st.core.toHealing (M.vote_time S.E (s + 1))
      (Wt (M.vote_time S.E (s + 1)) w).cache ⇢ c →
    Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E (s + 1)) w).st (M.vote_time S.E (s + 1)))
        (Wt (M.vote_time S.E (s + 1)) w).record c)
  confirmation : ∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
      (Wt (M.confirmation_time S.E s) w).st.core.toHealing (M.confirmation_time S.E s)
      (Wt (M.confirmation_time S.E s) w).cache ⇢ c →
    Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeConfirmationInputs M S rho s C w
      (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E s) w).st (M.confirmation_time S.E s))
        (Wt (M.confirmation_time S.E s) w).record c)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every read of round `q` (vote duties, confirmations, action reads and the opening
    proposer's), the finality root of the reader's store, staged from its node state in `Wt` at the
    read's instant, is an ancestor of `C`. -/
structure RoundCeilingAboveRootAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot, (M.opening_slot S.hc q) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (Wt (M.vote_time S.E d) w).st.core d)).toFG ⪯ C
  confirmation : ∀ s : Slot, (M.opening_slot S.hc q) ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.confirmation_time S.E s),
      Restated.Vocabulary.Protocol.confRoot M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (Wt (M.confirmation_time S.E s) w).st.core (M.confirmation_time S.E s)) ⪯ C
  action : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    M.get_fg_root (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w).st.core).toFG ⪯ C
  proposer : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) →
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc q)))).toFG ⪯ C

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every read of round `q` (vote duties, confirmations, action reads and the opening
    proposer's), `C` is in the filtered tree of the reader's store, staged from its node state in
    `Wt` at the read's instant. -/
structure RoundCeilingActiveAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (q : Round)
    (C : Block V) : Prop where
  voteDuty : ∀ d : Slot, (M.opening_slot S.hc q) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.vote_time S.E d),
      C ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (Wt (M.vote_time S.E d) w).st.core d)).toFG
  confirmation : ∀ s : Slot, (M.opening_slot S.hc q) ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.confirmation_time S.E s),
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (Wt (M.confirmation_time S.E s) w).st.core (M.confirmation_time S.E s))
  action : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    C ∈ M.get_filtered_block_tree (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w).st.core).toFG
  proposer : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) →
    C ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc q)))).toFG

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `C` is the ceiling of round `q` at height `hM`: a run block from which some thin honest head of
    the slot before round `q`'s opening slot descends, with `RoundCeilingAboveRootAtOn`,
    `RoundCeilingActiveAtOn` and `GateOffSeedConeWindowAtOn` holding, every anchor of round `q`'s
    readers an ancestor of `C`'s block, timing and horizon conditions, and every block confirmed at
    round `q`'s opening slot the erasure of a run block read along `W` through `Xb`. -/
structure RoundCeilingAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (hM : Height) (q : Round) (C : NamedBlock V) : Prop where
  roundPositive : 0 < q
  run : Restated.RunBlockOn M S rho W Xb C
  boundaryThinHead : Restated.ThinHonestHeadAtOn M S rho W Hs Xb hM ((M.opening_slot S.hc q) - 1) C.erase
  aboveRoot : Restated.RoundCeilingAboveRootAtOn M S rho Wt Hs q C.erase
  active : Restated.RoundCeilingActiveAtOn M S rho Wt Hs q C.erase
  postPreviousVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1)
  previousConfirmationInHorizon : M.confirmation_time S.E ((M.opening_slot S.hc q) - 1) ≤ rho.horizon
  postOpeningProposal : S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc q))
  postOpeningVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc q))
  roundConfirmationInHorizon : M.confirmation_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1) ≤ rho.horizon
  lastVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc q) - 1) fun X => C.erase ⪯ X
  openingStepInputs : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)), ∀ c : M.Cache,
    M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).st.core.toHealing
      (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1))
      (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).cache ⇢ c →
    Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho ((M.opening_slot S.hc q) - 1) C.erase w
      (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).st
        (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)))
        (Wt (M.vote_time S.E ((M.opening_slot S.hc q) - 1 + 1)) w).record c)
  roundInputs : ∀ s : Slot, (M.opening_slot S.hc q) ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    Restated.GoldfishConeSlotInputsOn M S rho Wt Hs s C.erase
  voteActive : ∀ d : Slot, (M.opening_slot S.hc q) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.vote_time S.E d),
      C.erase ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (Wt (M.vote_time S.E d) w).st.core d)).toFG
  actionActive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    C.erase ∈ M.get_filtered_block_tree (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w).st.core).toFG
  voteAnchor : ∀ d : Slot, (M.opening_slot S.hc q) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
        (Wt (M.vote_time S.E d) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
        (Wt (M.vote_time S.E d) w).record c
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ B →
        B ⪯ C.erase
  confirmationAnchor : ∀ s : Slot, (M.opening_slot S.hc q) - 1 ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
    ∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.confirmation_time S.E s) w).st.core.toHealing (M.confirmation_time S.E s)
        (Wt (M.confirmation_time S.E s) w).cache ⇢ c →
      ∀ B : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
          (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E s) w).st (M.confirmation_time S.E s))
            (Wt (M.confirmation_time S.E s) w).record c) ⇢ B →
        B ⪯ C.erase
  actionAnchor : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w) q,
      ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n q ⇢ a → a ⪯ C.erase
  proposerAnchorCeiling :
    S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
          (M.proposal_time S.E (M.opening_slot S.hc q))
          (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c →
        ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
            (M.mkNode (M.ns_setClock S.E
              (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st
              (M.proposal_time S.E (M.opening_slot S.hc q)))
              (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).record c)
            q ⇢ a → a ⪯ C.erase
  proposerActive :
    S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))) →
      C.erase ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (Wt (M.proposal_time S.E (M.opening_slot S.hc q)) (S.E.proposer (M.opening_slot S.hc q))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc q)))).toFG
  previousCarriers : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) v) (q - 1),
    ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
      B ⪯ C.erase
  gateOff : Restated.GateOffSeedConeWindowAtOn M S rho Wt Hs hM ((M.opening_slot S.hc q)) (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1)
  genuineRun : ∀ w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))), ∀ D : Block V,
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) w).st.core.toHealing
        (M.confirmation_time S.E ((M.opening_slot S.hc q)))
        (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) w).cache ⇢ c →
    Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract
          (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) w).st
            (M.confirmation_time S.E ((M.opening_slot S.hc q))))
            (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) w).record c).cache)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (Wt (M.confirmation_time S.E ((M.opening_slot S.hc q))) w).st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc q)))) ((M.opening_slot S.hc q)) D →
      ∃ Dn : NamedBlock V, Dn.erase = D ∧ Restated.RunBlockOn M S rho W Xb Dn

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every read of round `q + 1` (vote duties, confirmations from the boundary slot, the opening
    proposer's), the finality root of the reader's store, staged from its node state in `Wt` at the
    read's instant, is an ancestor of `C`. -/
structure RoundCeilingNextRootOrderAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot, (M.opening_slot S.hc (q + 1)) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    ∀ w ∈ Hs (M.vote_time S.E d),
      M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (Wt (M.vote_time S.E d) w).st.core d)).toFG ⪯ C
  confirmation : ∀ s : Slot, (M.opening_slot S.hc (q + 1)) - 1 ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    ∀ w ∈ Hs (M.confirmation_time S.E s),
      Restated.Vocabulary.Protocol.confRoot M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (Wt (M.confirmation_time S.E s) w).st.core (M.confirmation_time S.E s)) ⪯ C
  proposer : S.E.proposer ((M.opening_slot S.hc (q + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) →
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.proposal_time S.E (M.opening_slot S.hc (q + 1))) (S.E.proposer (M.opening_slot S.hc (q + 1)))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))).toFG ⪯ C

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- After `t_GST` and within the horizon, `GateOffSeedConeWindowAtOn` holds over round `q + 1`, and
    the boundary confirmers, round `q + 1`'s action readers and the readers at its opening proposal
    instant have, in their stores from the worlds `Wt`, `h_max = hM` and `h_j + 2 ≤ hM`. -/
structure RoundCeilingNextRegimeAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (hM : Height) (q : Round) : Prop where
  postOpeningProposal : S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))
  roundConfirmationInHorizon : M.confirmation_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) ≤ rho.horizon
  window : Restated.GateOffSeedConeWindowAtOn M S rho Wt Hs hM ((M.opening_slot S.hc (q + 1)))
    (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1)
  boundaryConfirmationFrontier : ∀ w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1)),
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) w).st.core
      (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1))).h_max = hM
  boundaryConfirmationGateOff : ∀ w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1)),
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1)) w).st.core
      (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1))).h_j + 2 ≤ hM
  actionFrontier : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.core).h_max = hM
  actionGateOff : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.core).h_j + 2 ≤ hM
  proposalFrontier : ∀ w ∈ Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))),
    (Wt (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.h_max = hM
  proposalGateOff : ∀ w ∈ Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))),
    (Wt (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.h_j + 2 ≤ hM

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `C` is a run block; some thin honest head and every honest vote of the slot before round
    `q + 1`'s opening slot descend, along `W`, from `C`'s block; every SG vote a member of
    `Hs (S.a q)` can select at a round-`q` action node state from `Wt (S.a q)` is an ancestor of
    `C`'s block; and the reads of round `q + 1` have finality roots that are ancestors of `C`'s
    block. -/
structure RoundCeilingBoundaryConeAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (hM : Height) (q : Round) (C : NamedBlock V) : Prop where
  run : Restated.RunBlockOn M S rho W Xb C
  boundaryThinHead : Restated.ThinHonestHeadAtOn M S rho W Hs Xb hM ((M.opening_slot S.hc (q + 1)) - 1) C.erase
  postAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q)
  postBoundaryVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)
  boundaryVotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc (q + 1)) - 1)
    fun X => C.erase ⪯ X
  previousCarriers : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v) q,
    ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
      B ⪯ C.erase
  rootOrder : Restated.RoundCeilingNextRootOrderAtOn M S rho Wt Hs q C.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At round `q + 1`: every outcome of each action reader's and of the opening proposer's anchor, at
    its node state from `Wt`, is `Cstar` or an ancestor of it, and every block confirmed at round
    `q + 1`'s opening slot from a confirmer's node state in `Wt` is the erasure of a run block read
    along `W` through `Xb`. -/
structure RoundCeilingStepResidualAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (hM : Height) (q : Round) (Cstar : Block V) : Prop where
  postOpeningProposal : S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))
  roundConfirmationInHorizon : M.confirmation_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) ≤ rho.horizon
  openingStepInputs : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)), ∀ c : M.Cache,
    M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).st.core.toHealing
      (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1))
      (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).cache ⇢ c →
    Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho ((M.opening_slot S.hc (q + 1)) - 1) Cstar w
      (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).st
        (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)))
        (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).record c)
  roundInputs : ∀ s : Slot, (M.opening_slot S.hc (q + 1)) ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    Restated.GoldfishConeSlotInputsOn M S rho Wt Hs s Cstar
  voteActive : ∀ d : Slot, (M.opening_slot S.hc (q + 1)) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    ∀ w ∈ Hs (M.vote_time S.E d),
      Cstar ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (Wt (M.vote_time S.E d) w).st.core d)).toFG
  actionActive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    Cstar ∈ M.get_filtered_block_tree
      (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.core).toFG
  voteAnchor : ∀ d : Slot, (M.opening_slot S.hc (q + 1)) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    ∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
        (Wt (M.vote_time S.E d) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
        (Wt (M.vote_time S.E d) w).record c
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ B →
        B ⪯ Cstar
  confirmationAnchor : ∀ s : Slot, (M.opening_slot S.hc (q + 1)) - 1 ≤ s →
    s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
      ∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc (Wt (M.confirmation_time S.E s) w).st.core.toHealing (M.confirmation_time S.E s)
          (Wt (M.confirmation_time S.E s) w).cache ⇢ c →
        ∀ B : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
            (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E s) w).st (M.confirmation_time S.E s))
              (Wt (M.confirmation_time S.E s) w).record c) ⇢ B →
          B ⪯ Cstar
  actionAnchor : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w) (q + 1),
      ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (q + 1) ⇢ a → a ⪯ Cstar
  proposerAnchorCeiling : S.E.proposer ((M.opening_slot S.hc (q + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) →
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
        (Wt (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
          (S.E.proposer (M.opening_slot S.hc (q + 1)))).cache ⇢ c →
      ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E
            (Wt (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
              (S.E.proposer (M.opening_slot S.hc (q + 1)))).st
            (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))
            (Wt (M.proposal_time S.E (M.opening_slot S.hc (q + 1)))
              (S.E.proposer (M.opening_slot S.hc (q + 1)))).record c)
          (q + 1) ⇢ a → a ⪯ Cstar
  proposerActive : S.E.proposer ((M.opening_slot S.hc (q + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) →
    Cstar ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (Wt (M.proposal_time S.E (M.opening_slot S.hc (q + 1))) (S.E.proposer (M.opening_slot S.hc (q + 1)))).st.core
      (M.proposal_time S.E (M.opening_slot S.hc (q + 1))))).toFG
  gateOff : Restated.GateOffSeedConeWindowAtOn M S rho Wt Hs hM ((M.opening_slot S.hc (q + 1)))
    (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1)
  genuineRun : ∀ w ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))), ∀ D : Block V,
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.core.toHealing
        (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))))
        (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) w).cache ⇢ c →
    Restated.Vocabulary.Protocol.GenuineConfirmationWith M
        (M.gradeContract
          (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) w).st
            (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))))
            (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) w).record c).cache)
        S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (Wt (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.core
          (M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))))) ((M.opening_slot S.hc (q + 1))) D →
      ∃ Dn : NamedBlock V, Dn.erase = D ∧ Restated.RunBlockOn M S rho W Xb Dn

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The set of the sets made of `C`'s block and one round-`q` action output `out v` for every member
    `v` of `Hs (S.a q)`, over every such choice `out`, each output the live confirmed block of an
    action node state staged from `Wt (S.a q)`. -/
def roundCeilingFrontierCandidatesOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (q : Round) (C : NamedBlock V) : DC.NDR (Finset (Block V)) :=
  { F | ∃ out : V → Block V,
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
        out v ∈ (fun n : M.N => n.live_confirmed) ''
          Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v) q) ∧
      F = insert C.erase ((Hs ((Restated.Vocabulary.Execution.Setup.a M S q))).image out) }

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every candidate set of `roundCeilingFrontierCandidatesOn`, its deepest block is `Cstar`;
    `Cstar` is a run block read through `Xb`, a descendant of `C` and of every round-`q` action
    output of every member of `Hs (S.a q)` read from `Wt (S.a q)`, and is `C` or the one output of
    some member. -/
structure RoundCeilingFrontierAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (q : Round) (C Cstar : NamedBlock V) : Prop where
  selected : ∀ F ∈ Restated.roundCeilingFrontierCandidatesOn M S rho Wt Hs q C, Block.deepest? F = some Cstar.erase
  run : Restated.RunBlockOn M S rho W Xb Cstar
  oldPreceq : C.erase ⪯ Cstar.erase
  outputsPreceq : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ B ∈ (fun n : M.N => n.live_confirmed) '' Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v) q, B ⪯ Cstar.erase
  source : Cstar = C ∨ ∃ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ B ∈ (fun n : M.N => n.live_confirmed) '' Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v) q, B = Cstar.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At round `q + 1`, read from the worlds `Wt`: the opening step's Goldfish cone vote inputs and
    every slot's inputs `GoldfishConeSlotInputsOn` hold for `C`, `C` is in the filtered tree of
    every vote duty store, and every vote and confirmation anchor is an ancestor of `C`. -/
structure RoundCeilingRelayFoldAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  openingStepInputs : ∀ w ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)), ∀ c : M.Cache,
    M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).st.core.toHealing
      (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1))
      (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).cache ⇢ c →
    Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho ((M.opening_slot S.hc (q + 1)) - 1) C w
      (M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).st
        (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)))
        (Wt (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1 + 1)) w).record c)
  roundInputs : ∀ s : Slot, (M.opening_slot S.hc (q + 1)) ≤ s → s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    Restated.GoldfishConeSlotInputsOn M S rho Wt Hs s C
  voteActive : ∀ d : Slot, (M.opening_slot S.hc (q + 1)) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    ∀ w ∈ Hs (M.vote_time S.E d),
      C ∈ M.get_filtered_block_tree (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (Wt (M.vote_time S.E d) w).st.core d)).toFG
  voteAnchor : ∀ d : Slot, (M.opening_slot S.hc (q + 1)) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
    ∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
        (Wt (M.vote_time S.E d) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
        (Wt (M.vote_time S.E d) w).record c
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ B →
        B ⪯ C
  confirmationAnchor : ∀ s : Slot, (M.opening_slot S.hc (q + 1)) - 1 ≤ s →
    s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) →
      ∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache,
        M.onPhaseTick S.E S.hc (Wt (M.confirmation_time S.E s) w).st.core.toHealing (M.confirmation_time S.E s)
          (Wt (M.confirmation_time S.E s) w).cache ⇢ c →
        ∀ B : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
            (M.mkNode (M.ns_setClock S.E (Wt (M.confirmation_time S.E s) w).st (M.confirmation_time S.E s))
              (Wt (M.confirmation_time S.E s) w).record c) ⇢ B →
          B ⪯ C

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The finality roots of the stores, staged from the worlds `Wt` at each read's instant, of the
    members of the set for that instant at the reads owned by round `q + 1`. -/
def seedRootReadCandidatesOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (q : Round) : Finset (Block V) :=
  (((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
        DecoupledConsensusModel.Proofs.HealingSurface.seedSlotRange)
      ((M.opening_slot S.hc (q + 1))) (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1))).biUnion
      (fun d => (Hs (M.vote_time S.E d)).image (fun w =>
        M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (Wt (M.vote_time S.E d) w).st.core d)).toFG))) ∪
    ((((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
          DecoupledConsensusModel.Proofs.HealingSurface.seedSlotRange)
        ((M.opening_slot S.hc (q + 1)) - 1) (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1)).biUnion
        (fun s => (Hs (M.confirmation_time S.E s)).image (fun w =>
          Restated.Vocabulary.Protocol.confRoot M (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (Wt (M.confirmation_time S.E s) w).st.core (M.confirmation_time S.E s))))) ∪
      (Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1))))).image (fun w =>
        M.get_fg_root (M.toHealing
          (Wt (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.core).toFG))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every anchor of round `q`'s opening proposer is an ancestor of `C`, the opening slot's voters'
    anchors are ancestors of `C`, `C` is an ancestor of every proposed parent, every confirmer's
    anchor is an ancestor of the proposal, and every round-`(q − 1)` action carrier is an ancestor
    of every proposed parent. -/
structure OpeningCeilingAlignedAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  sourceBelowCeiling :
    ∀ n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho ((M.opening_slot S.hc q)),
      ∀ a : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n q ⇢ a → a ⪯ C
  voteBelowCeiling : ∀ v ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc q))),
    ∀ B ∈ Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt M S rho v ((M.opening_slot S.hc q)), B ⪯ C
  ceilingBelowParent : ∀ Q ∈ Restated.Vocabulary.Proofs.HealingSurface.proposedParent M S rho ((M.opening_slot S.hc q)), C ⪯ Q
  confirmationBelowProposal : ∀ v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))),
    ∀ P : NamedBlock V,
      ∀ p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho ((M.opening_slot S.hc q)), p = some P →
      ∀ B ∈ Restated.Vocabulary.Internal.confirmationAnchorAt M S rho v ((M.opening_slot S.hc q)), B ⪯ P.erase
  previousCarriersBelowParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
    ∀ B ∈ Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt M S rho v (q - 1),
    ∀ Q ∈ Restated.Vocabulary.Proofs.HealingSurface.proposedParent M S rho ((M.opening_slot S.hc q)), B ⪯ Q

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some member of `Hs (S.a q)` has a round-`q` action node state staged from the world `wd` from
    which the SG vote selector can return `C`, with a run-block witness at height at least `hM − 1`
    in its tree descending from `C`; `C` erases a run block; and every round-`q` action carrier
    computed from `wd` of a member of `Hs (S.a q)` is an ancestor of `C`. -/
structure DeepestActionCarrierCeilingAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (hM : Height) (q : Round) (C : Block V) (wd : V → M.N) : Prop where
  sourceAndWitness : ∃ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) q,
      (∃ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 ∧
        M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ C) ∧
      ∃ Wn : NamedBlock V, Wn.erase ∈ n.st.core.T ∧ C ⪯ Wn.erase ∧
        Restated.RunBlockOn M S rho W Xb Wn ∧ hM - 1 ≤ (M.derive_named S.E S.cfg Wn).h
  run : ∃ D : NamedBlock V, D.erase = C ∧ Restated.RunBlockOn M S rho W Xb D
  previousCarriers : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) q,
    ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ B : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B → B ⪯ C

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member of `Hs (S.a (q − 1))` and every round-`(q − 1)` action node state staged from
    its node state in `Wt (S.a (q − 1))`, every outcome of the grade-2 selection there names a
    block; and the same for every member of `Hs (S.a q)` at round `q`, from `Wt (S.a q)`. -/
structure SeedRoundGradedAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (q : Round) :
    Prop where
  selectedPrev : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) v) (q - 1),
      ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (q - 1) ⇢ o →
        ∃ Q : Block V, o = some Q
  selected : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v) q,
      ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n q ⇢ o →
        ∃ Q : Block V, o = some Q

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every outcome of the grade-2 selection at every round-`q` action node state, staged from
    `Wt (S.a q)`, of a member of `Hs (S.a q)` names a block; and every member `w` of the set for the
    vote instant of round `q`'s last slot has a run block at height at least `hM − 1` that it grades
    2 at its store in `Wt (S.a q)` and that is in its vote duty store from `Wt (vote_time d)` for
    every slot `d` of round `q`. -/
def SeedRoundBandGradeAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (hM : Height) (q : Round) : Prop :=
  (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v) q,
      ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n q ⇢ o →
        ∃ Q : Block V, o = some Q) ∧
    ∀ w ∈ Hs (M.vote_time S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q)),
      ∃ Qn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Qn ∧ hM - 1 ≤ (M.derive_named S.E S.cfg Qn).h ∧
        (∀ g ∈ Restated.Vocabulary.Protocol.G2 M S.E
            (M.gradeView (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S q) w).st.core))
            S.hc q Qn.erase, g = true) ∧
          ∀ d : Slot, (M.opening_slot S.hc q) ≤ d → d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
            Qn.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (Wt (M.vote_time S.E d) w).st.core d).T

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Some run block along `W` at height at least `hM − 1` is an ancestor of every round-`q` carrier
    computed from the world `wd` of every member of `Hs (S.a q)`. -/
def SeedBandCarrierCoverAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (hM : Height) (q : Round) (wd : V → M.N) : Prop :=
  ∃ Qn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Qn ∧ hM - 1 ≤ (M.derive_named S.E S.cfg Qn).h ∧
    Restated.ActionCarriersCoverOn M S rho Hs q Qn.erase wd

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For round `c`, with carriers, anchors and heads read from the worlds `Wt`: the votes of the slot
    after round `c`'s opening slot form, along `W`, a cone over every round-`c` carrier of a member
    of `Hs (S.a c)`; every later vote-duty anchor of round `c` is compatible with every such
    carrier; and every head a voter of round `c` can compute erases a run block along `W` at height
    at least `hM − 1`. -/
structure SeedRoundDischargeAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (hM : Height) (c : Round) : Prop where
  claim1 : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (Wt (Restated.Vocabulary.Execution.Setup.a M S c) v) c,
    ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ A2 →
    ∀ A : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) A2 ⇢ A →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1) fun X => A ⪯ X
  anchorCompat : ∀ d : Slot, (M.opening_slot S.hc c) + 1 < d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
    ∀ w ∈ Hs (M.vote_time S.E d), ∀ cw : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
        (Wt (M.vote_time S.E d) w).cache ⇢ cw →
      let n := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
        (Wt (M.vote_time S.E d) w).record cw
      ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (M.round_of S.hc n.st.core.s) ⇢ B →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
      ∀ na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (Wt (Restated.Vocabulary.Execution.Setup.a M S c) v) c,
      ∀ A2 : Option (Block V), M.grade2_block_with (M.gradeContract na.cache) S.E S.hc
          (M.toHealing na.st.core) (M.round_of S.hc (M.toHealing na.st.core).s) ⇢ A2 →
      ∀ A : Block V, M.get_sg_vote_with (M.gradeContract na.cache) S.E S.hc (M.toHealing na.st.core)
          (M.round_of S.hc (M.toHealing na.st.core).s) A2 ⇢ A →
        B.compatible A = true
  headBand : ∀ d : Slot, (M.opening_slot S.hc c) ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
    ∀ w ∈ Hs (M.vote_time S.E d), ∀ cw : M.Cache,
      M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
        (Wt (M.vote_time S.E d) w).cache ⇢ cw →
      let n := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
        (Wt (M.vote_time S.E d) w).record cw
      ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
      ∃ Hn : NamedBlock V,
        Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧ hM - 1 ≤ (M.derive_named S.E S.cfg Hn).h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- At every round `c` with `base + 3 ≤ c` for a base round `base ≥ r0`, after `t_GST` and with
    `S.a (c + 2)` within the horizon, if `GateOffFrameAtOn` holds over `Hs` from round `base + 1` to
    `c + 2`, then `SeedRoundDischargeAtOn` holds at round `c`. -/
def SeedDischargeFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 : Round) : Prop :=
  ∀ (hM : Height) (base c : Round), r0 ≤ base → 1 ≤ c → base + 3 ≤ c →
    S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) → (Restated.Vocabulary.Execution.Setup.a M S (c + 2)) ≤ rho.horizon →
      Restated.GateOffFrameAtOn M S rho Wt Hs hM (base + 1) (c + 2) →
        Restated.SeedRoundDischargeAtOn M S rho W Wt Hs Xb hM c

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- In every window where `GateOffFrameAtOn` holds over `Hs`, every member of the set for a duty's
    vote instant has, at its vote-duty node state from `Wt`, every head it can compute erasing a run
    block, read along `W`, at height at least `hM − 1`. -/
def SeedBandReachFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 : Round) : Prop :=
  ∀ (hM : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) →
    (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon → Restated.GateOffFrameAtOn M S rho Wt Hs hM (c - 1) (c + 1) →
      ∀ d : Slot, (M.opening_slot S.hc c) ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
        ∀ w ∈ Hs (M.vote_time S.E d), ∀ cw : M.Cache,
          M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
            (Wt (M.vote_time S.E d) w).cache ⇢ cw →
          let n := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
            (Wt (M.vote_time S.E d) w).record cw
          ∀ Tt : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tt →
          ∀ L : Finset (GoldfishVote V),
            M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
          ∀ L' : Finset (GoldfishVote V),
            M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
          ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
              (M.toHealing n.st.core) Tt L L' (n.st.core.s - 1) ⇢ Hd →
          ∃ Hn : NamedBlock V,
            Hn.erase = Hd ∧ Restated.RunBlockOn M S rho W Xb Hn ∧
              hM - 1 ≤ (M.derive_named S.E S.cfg Hn).h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- In every window where `GateOffFrameAtOn` holds over `Hs`, every member of `Hs (S.a c)` has a raw
    grade-2 block at every round-`c` action node state staged from its node state in `Wt (S.a c)`. -/
def SeedRawG2FromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (r0 : Round) : Prop :=
  ∀ (hM : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) →
    (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon → Restated.GateOffFrameAtOn M S rho Wt Hs hM (c - 1) (c + 1) →
      ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (Wt (Restated.Vocabulary.Execution.Setup.a M S c) v) c,
          Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S n c

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- In every window where `GateOffFrameAtOn` holds over `Hs`, every anchor a voter can read at its
    vote-duty node state from `Wt` is compatible with every SG vote of a round-`c` action node
    state, staged from `Wt (S.a c)`, of a member of `Hs (S.a c)`, unless that node state has no raw
    grade-2 block at round `c`. -/
def SeedAnchorCompatFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Wt : Time → V → M.N)
    (Hs : Int → Finset V) (r0 : Round) :
    Prop :=
  ∀ (hM : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) →
    (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon → Restated.GateOffFrameAtOn M S rho Wt Hs hM (c - 1) (c + 1) →
      ∀ d : Slot, (M.opening_slot S.hc c) + 1 ≤ d → d ≤ (M.opening_slot S.hc (c + 1)) - 1 →
        ∀ w ∈ Hs (M.vote_time S.E d), ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)),
          ∀ cw : M.Cache,
            M.onPhaseTick S.E S.hc (Wt (M.vote_time S.E d) w).st.core.toHealing (M.vote_time S.E d)
              (Wt (M.vote_time S.E d) w).cache ⇢ cw →
          let nw := M.mkNode (M.ns_setClock S.E (Wt (M.vote_time S.E d) w).st (M.vote_time S.E d))
            (Wt (M.vote_time S.E d) w).record cw
          ∀ B : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S nw
              (M.round_of S.hc nw.st.core.s) ⇢ B →
          ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
              (Wt (Restated.Vocabulary.Execution.Setup.a M S c) v) c,
          let gc := M.gradeContract n.cache
          let st := (M.toHealing n.st.core)
          let k := (M.round_of S.hc st.s)
          ∀ A2 : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
          ∀ G : Block V, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ G →
          B.compatible G = true ∨
            ¬Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 M S n c

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- The regime of round `q` at height `hM`: timing and horizon conditions, every member of
    `Hs (S.a q)` with `h_max = hM` and `h_j + 2 ≤ hM` in its store in `Wt (S.a q)`, round `q` ready
    for grading, `SelectedG2SettledAtOn` at round `q`, and `RoundCeilingNextRegimeAtOn` at round
    `q`. -/
structure SeedRoundRegimeAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (hM : Height)
    (q : Round) : Prop where
  postAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q)
  postOpeningProposal : S.E.t_GST ≤ M.proposal_time S.E ((M.opening_slot S.hc q))
  postBoundaryVote : S.E.t_GST ≤ M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1)
  openingConfirmationInHorizon : M.confirmation_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon
  boundaryConfirmationInHorizon :
    M.confirmation_time S.E ((M.opening_slot S.hc (q + 1)) - 1) ≤ rho.horizon
  frontier : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v).st.h_max = hM
  gate : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
    (Wt (Restated.Vocabulary.Execution.Setup.a M S q) v).st.h_j + 2 ≤ hM
  ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho q
  settled : Restated.SelectedG2SettledAtOn M S rho Wt Hs q
  next : Restated.RoundCeilingNextRegimeAtOn M S rho Wt Hs hM q

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every head that a committee member of round `q`'s last slot, in the set for that slot's vote
    instant, voted at that slot has height at least `hM − 1`; and some run block `C`, with a
    run-block witness at height at least `hM − 1` as a descendant, is a descendant of every
    round-`q` carrier computed from the world `wd` of a member of `Hs (S.a q)` and an ancestor of
    every such head. -/
structure SeedBoundaryAdoptionAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (hM : Height) (q : Round) (wd : V → M.N) : Prop where
  headThin : ∀ X : NamedBlock V,
    Restated.NamedHonestHeadOn M S rho W (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
      ((M.opening_slot S.hc (q + 1)) - 1) X →
    hM - 1 ≤ (M.derive_named S.E S.cfg X).h
  entry : ∃ C : NamedBlock V, Restated.RunBlockOn M S rho W Xb C ∧
    (∃ Wn : NamedBlock V, Restated.RunBlockOn M S rho W Xb Wn ∧ C.erase ⪯ Wn.erase ∧
      hM - 1 ≤ (M.derive_named S.E S.cfg Wn).h) ∧
    (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wd v) q,
      ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        B ⪯ C.erase) ∧
    ∀ X : NamedBlock V,
      Restated.NamedHonestHeadOn M S rho W (fun _ => Hs (M.vote_time S.E ((M.opening_slot S.hc (q + 1)) - 1))) Xb
        ((M.opening_slot S.hc (q + 1)) - 1) X →
      C.erase ⪯ X.erase

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Either the largest `h_max` over `Hs (S.a endpointRound)` in `Wi (S.a endpointRound)` exceeds
    `hM`; or some member `u` of `Hs read`, at a post-GST `read` up to the endpoint with
    `S.a base ≤ read` or `u` in the set for `S.a base`, holds in `Wt read` a fixed-height
    justification root at `hM`; or two opening proposals `Q` and `Next` of carrier rounds
    `entry < q` exist, `Q` a graded run block at height `hM` that is an ancestor of `Next`'s parent
    at the same height. -/
def HeightProgressSeedOutcomeOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt Wi : Time → V → M.N) (Hs : Int → Finset V)
    (Xb : Finset V) (hM : Height) (base endpointRound : Round) (delayExtra : Nat := 0) : Prop :=
  hM < ((Hs (Restated.Vocabulary.Execution.Setup.a M S endpointRound)).sup fun v =>
      (Wi (Restated.Vocabulary.Execution.Setup.a M S endpointRound) v).st.core.h_max) ∨
    (∃ (u : V) (read : Time), u ∈ Hs read ∧ S.E.t_GST ≤ read ∧ read ≤ (Restated.Vocabulary.Execution.Setup.a M S endpointRound) ∧
      ((Restated.Vocabulary.Execution.Setup.a M S base) ≤ read ∨ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base))) ∧
        Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb hM u read (Wt read)) ∨
      ∃ (entry : Round) (q : Round) (Q : NamedBlock V) (Next : NamedBlock V) (Parent : NamedBlock V),
        base + 1 ≤ entry ∧ entry + 2 + delayExtra ≤ q ∧ q ≤ endpointRound ∧
          Restated.ProposerCarrierAtOn M S Hs q ∧
            (∃ c : M.Cache, M.onPhaseTick S.E S.hc
                  (Wt (M.proposal_time S.E (M.opening_slot S.hc entry))
                    (S.E.proposer (M.opening_slot S.hc entry))).st.core.toHealing
                  (M.proposal_time S.E (M.opening_slot S.hc entry))
                  (Wt (M.proposal_time S.E (M.opening_slot S.hc entry))
                    (S.E.proposer (M.opening_slot S.hc entry))).cache ⇢ c ∧
                M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
                  (S.node (S.E.proposer (M.opening_slot S.hc entry)))
                  (M.ns_setClock S.E
                    (Wt (M.proposal_time S.E (M.opening_slot S.hc entry))
                      (S.E.proposer (M.opening_slot S.hc entry))).st
                    (M.proposal_time S.E (M.opening_slot S.hc entry))) ⇢ some Q) ∧
              (∀ v ∈ Hs (M.domain S.E S.hc (q - 1) Phase.g2),
                Q.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                    (Wt (M.domain S.E S.hc (q - 1) Phase.g2) v) ∧
                  ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
                    (Wt (M.domain S.E S.hc (q - 1) Phase.g2) v).st (q - 1) Phase.g2 Q.erase ⇢ b →
                    b = true) ∧ Restated.RunBlockOn M S rho W Xb Q ∧
                (M.derive_named S.E S.cfg Q).h = hM ∧
                  (∃ c : M.Cache, M.onPhaseTick S.E S.hc
                        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
                          (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
                        (M.proposal_time S.E (M.opening_slot S.hc q))
                        (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
                          (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c ∧
                      M.proposal_with (M.gradeContract c) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
                        (S.node (S.E.proposer (M.opening_slot S.hc q)))
                        (M.ns_setClock S.E
                          (Wt (M.proposal_time S.E (M.opening_slot S.hc q))
                            (S.E.proposer (M.opening_slot S.hc q))).st
                          (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some Next) ∧
                    Next.parent? = some Parent ∧ Q.Preceq Parent ∧
                      (M.derive_named S.E S.cfg Parent).h = (M.derive_named S.E S.cfg Q).h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- From every post-GST base round after `r0`, with `hM` the largest `h_max` over `Hs (S.a base)` in
    `Wi (S.a base)`: if every member of `Hs (S.a base)` has `h_max = hM` and `h_j + 2 ≤ hM` in
    `Wt (S.a base)` and the seed window ends within the horizon, then `HeightProgressSeedOutcomeOn`
    holds at `hM`. -/
def HeightProgressSeedFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt Wi : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 gap : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ base : Round, r0 ≤ base → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base) →
    ∀ hM : Height, ((Hs (Restated.Vocabulary.Execution.Setup.a M S base)).sup fun v =>
        (Wi (Restated.Vocabulary.Execution.Setup.a M S base) v).st.core.h_max) = hM →
    (∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base)),
      (Wt (Restated.Vocabulary.Execution.Setup.a M S base) w).st.core.h_max = hM) →
    (∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S base)),
      (Wt (Restated.Vocabulary.Execution.Setup.a M S base) w).st.core.h_j + 2 ≤ hM) →
    (Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra)) ≤ rho.horizon →
      Restated.HeightProgressSeedOutcomeOn M S rho W Wt Wi Hs Xb hM base
        (base + seedLag gap delayExtra) delayExtra

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For every member of `Hs (S.a (q' − 1))`, every round-`(q' − 1)` action node state `n` staged
    from its node state in `wa`, and every block that some outcome of `n`'s FG source names, that
    block's height in `n`'s store is at most the height of `B'`'s parent. -/
structure SeedPredPromotionInputsAtOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V)
    (hM : Height) (q q' : Round) (B B' : NamedBlock V) (wa : V → M.N) : Prop where
  sourceHeightLeNextOpeningParent : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (wa v) (q' - 1), ∀ Q : Block V,
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n (q' - 1) ⇢ some Q →
      ((M.toHealing n.st.core).σ Q).h ≤ (M.derive_named S.E S.cfg B'.parent).h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- For all carrier rounds `q` and `q'` with ceilings `RoundCeilingAtOn` and opening windows
    `NamedGateOffOpeningWindowAtOn`, `q + 2 + delayExtra ≤ q'` and `r0 + 2 ≤ q'`, if the stores from
    `S.a (q' − 2)` to `S.a q'` in `Wt` have `h_j + 2 ≤ hM` and `h_max = hM`, and `B`'s block is
    graded 2 in round `q' − 1` and active at round `q' − 1`'s action readers, then
    `SeedPredPromotionInputsAtOn` holds at the world `Wt (S.a (q' − 1))`. -/
def SeedPredPromotionInputsOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ (hM : Height) (q q' : Round) (C C' B B' : NamedBlock V), 2 ≤ hM →
    Restated.SeedRoundGradedAtOn M S rho Wt Hs q → Restated.ProposerCarrierAtOn M S Hs q →
      Restated.RoundCeilingAtOn M S rho W Wt Hs Xb hM q C → Restated.NamedGateOffOpeningWindowAtOn M S rho Wt Hs hM q B →
        (M.derive_named S.E S.cfg B).h = hM - 1 → q + 2 + delayExtra ≤ q' → r0 + 2 ≤ q' →
          Restated.ProposerCarrierAtOn M S Hs q' → Restated.RoundCeilingAtOn M S rho W Wt Hs Xb hM q' C' →
            Restated.NamedGateOffOpeningWindowAtOn M S rho Wt Hs hM q' B' → S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q' - 2)) →
              (Restated.Vocabulary.Execution.Setup.a M S q') ≤ rho.horizon →
                (∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (q' - 2)) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S q') → ∀ w ∈ Hs read,
                  (Wt read w).st.h_j + 2 ≤ hM ∧ (Wt read w).st.h_max = hM) →
                  Restated.RunBlockOn M S rho W Xb B →
                    (∀ v ∈ Hs (M.domain S.E S.hc (q' - 1) Phase.g2),
                      B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                          (Wt (M.domain S.E S.hc (q' - 1) Phase.g2) v) ∧
                        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
                          (Wt (M.domain S.E S.hc (q' - 1) Phase.g2) v).st (q' - 1) Phase.g2 B.erase ⇢ b →
                          b = true) →
                    (∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1))),
                      B.erase ∈ M.get_filtered_block_tree
                        (Wt (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)) w).st.core.toHealing.toFG) →
                      Restated.SeedPredPromotionInputsAtOn M S rho Hs hM q q' B B'
                        (Wt (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- From every post-GST base round `base ≥ r0` and carrier round `q` with a ceiling
    `RoundCeilingAtOn` and an opening window `NamedGateOffOpeningWindowAtOn`, if the largest `h_max`
    over `Hs` stays `hM` from `S.a base` to the endpoint's action instant, in the worlds `Wi`, and
    the window's stores in `Wt` have `h_j + 2 ≤ hM` and `h_max = hM`, then
    `HeightProgressSeedOutcomeOn` holds at `hM`. -/
def SeedPredCloserFromOn (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (Wt Wi : Time → V → M.N) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 gap : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ (base q : Round) (Cq P : NamedBlock V), r0 ≤ base → base + 4 ≤ q →
    q + 2 * gap + 6 + 2 * delayExtra ≤ base + seedLag gap delayExtra →
      S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S base) → (Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra)) ≤ rho.horizon →
        ∀ hM : Height, ((Hs (Restated.Vocabulary.Execution.Setup.a M S base)).sup fun v =>
            (Wi (Restated.Vocabulary.Execution.Setup.a M S base) v).st.core.h_max) = hM →
        ((Hs (Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra))).sup fun v =>
            (Wi (Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra)) v).st.core.h_max) ≤
          hM →
          2 ≤ hM →
            (∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S (base + 1)) ≤ read → read ≤ (Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra)) →
              ∀ w ∈ Hs read,
                (read + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra)) ∨
                    w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (base + seedLag gap delayExtra)))) →
                (Wt read w).st.core.h_j + 2 ≤ hM ∧ (Wt read w).st.core.h_max = hM) →
              Restated.SeedRoundGradedAtOn M S rho Wt Hs q → Restated.ProposerCarrierAtOn M S Hs q →
                Restated.RoundCeilingAtOn M S rho W Wt Hs Xb hM q Cq →
                  Restated.NamedGateOffOpeningWindowAtOn M S rho Wt Hs hM q P →
                    (M.derive_named S.E S.cfg P).h = hM - 1 →
                      Restated.HeightProgressSeedOutcomeOn M S rho W Wt Wi Hs Xb hM
                        base (base + seedLag gap delayExtra) delayExtra

end

/-! ## Agreement at `Record.Model.vocabulary` -/

open scoped DC in
/-- `b` is an outcome of `pure a` exactly when `a = b`. -/
private theorem returns_pure_eq₄₂c {α : Type} (a b : α) : (pure a : DC.NDRE α) ⇢ b ↔ a = b := by
  rw [Record.returns_pure, eq_comm]

open scoped DC in
/-- At `Record.Model.vocabulary`, the phase tick is `pure` of `Protocol.onPhaseTick`. -/
private theorem vocabulary_onPhaseTick₄₂c (E : Env V) (hc : Protocol.HealConfig)
    (st : (Record.Model.vocabulary (V := V)).HS) (t : Time) (c : (Record.Model.vocabulary (V := V)).Cache) :
    (Record.Model.vocabulary (V := V)).onPhaseTick E hc st t c =
      (pure (Protocol.onPhaseTick E hc st t c) : DC.NDRE (Record.Model.vocabulary (V := V)).Cache) :=
  rfl

open scoped DC in
/-- At `Record.Model.vocabulary`, the SG root is `pure` of `Protocol.get_sg_root_with`. -/
private theorem vocabulary_get_sg_root_with₄₂c (gc : (Record.Model.vocabulary (V := V)).Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : (Record.Model.vocabulary (V := V)).HS) (r : Round) :
    (Record.Model.vocabulary (V := V)).get_sg_root_with gc E hc st r =
      (pure (Protocol.get_sg_root_with gc E hc st r) : DC.NDRE (Block V)) :=
  rfl

open DecoupledConsensusModel.Execution in
/-- At `Record.Model.vocabulary`, the node state built from `v`'s node state in the world before `t`,
    with the clock set to `t` and the cache the phase tick returns, is
    `confirmationReadAt S rho v t`. -/
private theorem confReadAt_vocabulary₄₂c (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    (Record.Model.vocabulary (V := V)).mkNode
        ((Record.Model.vocabulary (V := V)).ns_setClock S.E
          (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho t v)) t)
        (Record.Model.N.record (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho t v))
        (Protocol.onPhaseTick S.E S.hc
          (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho t v)).core.toHealing t
          (Record.Model.N.cache (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho t v))) =
      NamedActionReads.confirmationReadAt S rho v t := by
  have hmem : _ ∈ Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt
      Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v t :=
    ⟨_, by rw [Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq]; exact Set.mem_singleton _,
      _, (Record.returns_pure _ _).2 rfl, rfl⟩
  rw [Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq] at hmem
  exact hmem

/-- Splits an equivalence of structures into its fields and closes each by the `record_vocabulary`
    lemmas, the one-outcome lemmas of this file and definitional equality. -/
syntax "record_vocabulary_struct_iff₄₂c" : tactic
macro_rules
  | `(tactic| record_vocabulary_struct_iff₄₂c) =>
    `(tactic| (constructor <;> intro h <;> cases h <;> constructor <;>
        (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
          Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
          vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
          forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *) <;>
        first
        | assumption
        | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
            forall_apply_eq_imp_iff] at *; assumption)))

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- `Restated.FixedHeightJustificationRootOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedHeightJustificationRootOn`. -/
@[record_vocabulary]
theorem FixedHeightJustificationRootOn_vocabulary_eq (S : Setup V) (rho : Run V) (Xb : Finset V) (st : Store V) (H : Height) :
    _root_.DecoupledConsensusModel.Sts.FixedHeightJustificationRootOn (V := V) S rho Xb st H ↔ Restated.FixedHeightJustificationRootOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Xb st H :=
  by
  record_vocabulary_struct_iff

/-- `Restated.FixedHeightRootTargetOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedHeightRootTargetOn`. -/
@[record_vocabulary]
theorem FixedHeightRootTargetOn_vocabulary_eq (S : Setup V) (rho : Run V) (Xb : Finset V) (st : Store V) (P : Block V) (H : Height) :
    _root_.DecoupledConsensusModel.Sts.FixedHeightRootTargetOn (V := V) S rho Xb st P H ↔ Restated.FixedHeightRootTargetOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Xb st P H :=
  by
  record_vocabulary_struct_iff

/-- `Restated.FixedHeightJustificationRootAtReadOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedHeightJustificationRootAtReadOn`. -/
@[record_vocabulary]
theorem FixedHeightJustificationRootAtReadOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (H : Height) (w : V) (read : Time) :
    _root_.DecoupledConsensusModel.Sts.FixedHeightJustificationRootAtReadOn (V := V) S rho Hs Xb H w read ↔ Restated.FixedHeightJustificationRootAtReadOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Hs Xb H w read
      (_root_.DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime S rho read) :=
  by
  record_vocabulary_struct_iff

/-- `Restated.FixedHeightRootInterferenceAtReadOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedHeightRootInterferenceAtReadOn`. -/
@[record_vocabulary]
theorem FixedHeightRootInterferenceAtReadOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (H : Height) (w : V) (read : Time) (P : Block V) :
    _root_.DecoupledConsensusModel.Sts.FixedHeightRootInterferenceAtReadOn (V := V) S rho Hs Xb H w read P ↔ Restated.FixedHeightRootInterferenceAtReadOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Hs Xb H w read
      (_root_.DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime S rho read) P :=
  by
  record_vocabulary_struct_iff

/-- `Restated.HonestHMaxCarrierAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HonestHMaxCarrierAtOn`. -/
@[record_vocabulary]
theorem HonestHMaxCarrierAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (t : Time) (H : Height) (holder : V) (carrier : Block V) :
    _root_.DecoupledConsensusModel.Sts.HonestHMaxCarrierAtOn (V := V) S rho Hs Xb t H holder carrier ↔ Restated.HonestHMaxCarrierAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Hs Xb t
      (_root_.DecoupledConsensusModel.Execution.NamedRun.readAt S rho t) H holder carrier :=
  by
  record_vocabulary_struct_iff

/-- `Restated.FixedRootPreparedTargetDataOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedRootPreparedTargetDataOn`. -/
@[record_vocabulary]
theorem FixedRootPreparedTargetDataOn_vocabulary_eq (S : Setup V) (rho : Run V) (Xb : Finset V) (H : Height) (fixed pre : NamedStore V) (target : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.FixedRootPreparedTargetDataOn (V := V) S rho Xb H fixed pre target ↔ Restated.FixedRootPreparedTargetDataOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Xb H fixed pre target :=
  by
  record_vocabulary_struct_iff

/-- At `Record.Model.vocabulary`, `NamedGradeFormsAtOn S rho Hs r C` holds exactly when every member
    of `Hs (domain r .g2)` has `C` active, with every outcome of its round-`r` grade-2 store grade
    for `C` `true`, at its node state before round `r`'s grade-2 domain instant. -/
private theorem namedGradeFormsAt_iff_body_vocabulary₄₂c (S : Setup V) (rho : Run V)
    (Hs : Int → Finset V) (r : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.NamedGradeFormsAtOn (V := V) S rho Hs r C ↔
      ∀ v ∈ Hs ((Record.Model.vocabulary (V := V)).domain S.E S.hc r Phase.g2),
        C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree Record.Model.vocabulary
            (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).domain S.E S.hc r Phase.g2) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade Record.Model.vocabulary S.E S.hc
            (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).domain S.E S.hc r Phase.g2) v))
            r Phase.g2 C ⇢ b → b = true :=
  NamedGradeFormsAtOn_vocabulary_eq S rho Hs r C

/-- At `Record.Model.vocabulary`, `proposedBlockAt S rho s = some P` exactly when the proposal duty of
    slot `s`'s proposer, at its node state before `s`'s proposal instant staged with some outcome of
    the cache update, can return `some P`. -/
private theorem proposedBlockAt_iff_body_vocabulary₄₂c (S : Setup V) (rho : Run V) (s : Slot)
    (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Statements.Instantiation.proposedBlockAt S rho s = some P ↔
      ∃ c : (Record.Model.vocabulary (V := V)).Cache,
        (Record.Model.vocabulary (V := V)).onPhaseTick S.E S.hc
          (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
            ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s))).core.toHealing
          ((Record.Model.vocabulary (V := V)).proposal_time S.E s)
          (Record.Model.N.cache (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
            ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s))) ⇢ c ∧
        (Record.Model.vocabulary (V := V)).proposal_with
          ((Record.Model.vocabulary (V := V)).gradeContract c)
          Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
          ((Record.Model.vocabulary (V := V)).ns_setClock S.E
            (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s)))
            ((Record.Model.vocabulary (V := V)).proposal_time S.E s)) ⇢ some P := by
  unfold _root_.DecoupledConsensusModel.Statements.Instantiation.proposedBlockAt
    _root_.DecoupledConsensusModel.Statements.Instantiation.proposerReadAt
  rw [← confReadAt_vocabulary₄₂c S rho (S.E.proposer s)]
  constructor
  · intro h
    exact ⟨_, (Record.returns_pure _ _).2 rfl, (Record.returns_pure _ _).2 h.symm⟩
  · rintro ⟨c, hc, hP⟩
    obtain rfl := (Record.returns_pure _ _).1 hc
    exact ((Record.returns_pure _ _).1 hP).symm

/-- `Restated.NamedRawOpeningLifecycleAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedRawOpeningLifecycleAtOn`. -/
@[record_vocabulary]
theorem NamedRawOpeningLifecycleAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedRawOpeningLifecycleAtOn (V := V) S rho Hs Xb r P ↔ Restated.NamedRawOpeningLifecycleAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb r P :=
  by
  constructor
  · intro h
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc r) P).1 h.proposal
    cases h
    constructor
    case proposal => exact hp
    all_goals
      ((try simp only [namedGradeFormsAt_iff_body_vocabulary₄₂c] at *);
       (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq, returns_pure_eq₄₂c, forall_eq'] at *);
       assumption)
  · intro h
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc r) P).2 h.proposal
    cases h
    constructor
    case proposal => exact hp
    all_goals
      ((try simp only [namedGradeFormsAt_iff_body_vocabulary₄₂c] at *);
       (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq, returns_pure_eq₄₂c, forall_eq'] at *);
       assumption)

/-- At `Record.Model.vocabulary`, `namedG1At S rho w q B` holds exactly when every outcome of the
    round-`q` grade-1 store grade for `B` at `w`'s store before round `q`'s grade-1 domain instant
    is `true`. -/
private theorem namedG1At_iff_body_vocabulary₄₂c (S : Setup V) (rho : Run V) (w : V) (q : Round)
    (B : Block V) :
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.namedG1At S rho w q B ↔
      ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade Record.Model.vocabulary S.E S.hc
        (NamedRun.stateBeforeTime S rho
          ((Record.Model.vocabulary (V := V)).domain S.E S.hc q Phase.g1) w).st q Phase.g1 B ⇢ b →
        b = true := by
  rw [Vocabulary.Proofs.HealingSurface.namedG1At_vocabulary_eq]
  unfold Restated.Vocabulary.Proofs.HealingSurface.namedG1At
  rw [Vocabulary.Internal.PhaseGrades.readAt_vocabulary_eq]
  exact ⟨fun h => h _ rfl, fun h n hn => by obtain rfl : n = _ := hn; exact h⟩

/-- At `Record.Model.vocabulary`, a property holds of every block the SG vote selector can return at a
    round-`r` action node state staged from `v`'s node state before `S.a r` exactly when it holds of
    `v`'s action carrier. -/
private theorem actionCarrierFrom_vocabulary₄₂c (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (p : Block V → Prop) :
    (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
        (NamedRun.stateBeforeTime S rho (S.a r) v) r,
      ∀ g : Option (Block V), (Record.Model.vocabulary (V := V)).grade2_block_with
          ((Record.Model.vocabulary (V := V)).gradeContract n.cache) S.E S.hc
          ((Record.Model.vocabulary (V := V)).toHealing n.st.core)
          ((Record.Model.vocabulary (V := V)).round_of S.hc
            ((Record.Model.vocabulary (V := V)).toHealing n.st.core).s) ⇢ g →
      ∀ A : Block V, (Record.Model.vocabulary (V := V)).get_sg_vote_with
          ((Record.Model.vocabulary (V := V)).gradeContract n.cache) S.E S.hc
          ((Record.Model.vocabulary (V := V)).toHealing n.st.core)
          ((Record.Model.vocabulary (V := V)).round_of S.hc
            ((Record.Model.vocabulary (V := V)).toHealing n.st.core).s) g ⇢ A → p A) ↔
      p (actionSGBlockAt S rho v r) := by
  rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]
  constructor
  · intro h
    exact h _ rfl _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
  · intro h n hn g hg A hA
    obtain rfl : n = _ := hn
    obtain rfl := (Record.returns_pure _ _).1 hg
    obtain rfl := (Record.returns_pure _ _).1 hA
    exact h

/-- At `Record.Model.vocabulary`, a property holds of the parent of every proposal input of slot `s`'s
    proposer, staged from its node state before `s`'s proposal instant, exactly when it holds of the
    proposed parent of `s`. -/
private theorem proposedParentFrom_vocabulary₄₂c (S : Setup V) (rho : Run V) (s : Slot)
    (p : Block V → Prop) :
    (∀ c : (Record.Model.vocabulary (V := V)).Cache,
        (Record.Model.vocabulary (V := V)).onPhaseTick S.E S.hc
          (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
            ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s))).core.toHealing
          ((Record.Model.vocabulary (V := V)).proposal_time S.E s)
          (Record.Model.N.cache (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
            ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s))) ⇢ c →
      ∀ I : Protocol.ProposalInput V,
        Restated.Vocabulary.Protocol.proposal_input_with Record.Model.vocabulary
          ((Record.Model.vocabulary (V := V)).gradeContract c) S.E S.hc (S.node (S.E.proposer s))
          ((Record.Model.vocabulary (V := V)).toHealing ((Record.Model.vocabulary (V := V)).mkNode
            ((Record.Model.vocabulary (V := V)).ns_setClock S.E
              (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
                ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s)))
              ((Record.Model.vocabulary (V := V)).proposal_time S.E s))
            (Record.Model.N.record (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).proposal_time S.E s) (S.E.proposer s))) c).st.core) ⇢ I →
        p I.parent) ↔
      p (_root_.DecoupledConsensusModel.Proofs.HealingSurface.proposedParent S rho s) := by
  constructor
  · intro h
    have h' := h _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)
    unfold _root_.DecoupledConsensusModel.Proofs.HealingSurface.proposedParent
      _root_.DecoupledConsensusModel.Proofs.HealingSurface.proposalInputAt
      _root_.DecoupledConsensusModel.Statements.Instantiation.proposerReadAt
    rw [← confReadAt_vocabulary₄₂c S rho (S.E.proposer s)]
    exact h'
  · intro h c hc I hI
    obtain rfl := (Record.returns_pure _ _).1 hc
    obtain rfl := (Record.returns_pure _ _).1 hI
    unfold _root_.DecoupledConsensusModel.Proofs.HealingSurface.proposedParent
      _root_.DecoupledConsensusModel.Proofs.HealingSurface.proposalInputAt
      _root_.DecoupledConsensusModel.Statements.Instantiation.proposerReadAt at h
    rw [← confReadAt_vocabulary₄₂c S rho (S.E.proposer s)] at h
    exact h

/-- `Restated.FixedRootPreparedParentCandidateOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedRootPreparedParentCandidateOn`. -/
@[record_vocabulary]
theorem FixedRootPreparedParentCandidateOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (H : Height) (q : Round) (w : V) (read : Time) (A : Block V) (target : NamedBlock V) (ceiling actionCeiling : Block V) (actionWitness : V) (fixed pre : NamedStore V) (source : Store V) :
    _root_.DecoupledConsensusModel.Sts.FixedRootPreparedParentCandidateOn (V := V) S rho Hs Xb H q w read A target ceiling actionCeiling actionWitness fixed pre source ↔ Restated.FixedRootPreparedParentCandidateOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb H q w read A target ceiling actionCeiling actionWitness fixed pre source
        (NamedRun.stateBeforeTime S rho (S.a (q - 1))) := by
  have hEq : actionCeiling = actionSGBlockAt S rho actionWitness (q - 1) ↔
      ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
          (NamedRun.stateBeforeTime S rho (S.a (q - 1)) actionWitness) (q - 1),
        ∃ g : Option (Block V), (Record.Model.vocabulary (V := V)).grade2_block_with
            ((Record.Model.vocabulary (V := V)).gradeContract n.cache) S.E S.hc
            ((Record.Model.vocabulary (V := V)).toHealing n.st.core)
            ((Record.Model.vocabulary (V := V)).round_of S.hc
              ((Record.Model.vocabulary (V := V)).toHealing n.st.core).s) ⇢ g ∧
          (Record.Model.vocabulary (V := V)).get_sg_vote_with
            ((Record.Model.vocabulary (V := V)).gradeContract n.cache) S.E S.hc
            ((Record.Model.vocabulary (V := V)).toHealing n.st.core)
            ((Record.Model.vocabulary (V := V)).round_of S.hc
              ((Record.Model.vocabulary (V := V)).toHealing n.st.core).s) g ⇢ actionCeiling := by
    constructor
    · intro hC
      have hn : actionStoreAt S rho actionWitness (q - 1) ∈
          Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
            (NamedRun.stateBeforeTime S rho (S.a (q - 1)) actionWitness) (q - 1) := by
        rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]
        exact Set.mem_singleton _
      exact ⟨_, hn, _, (Record.returns_pure _ _).2 rfl, (Record.returns_pure _ _).2 hC⟩
    · rintro ⟨n, hn, g, hg, hC⟩
      rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq] at hn
      obtain rfl : n = _ := hn
      obtain rfl := (Record.returns_pure _ _).1 hg
      exact (Record.returns_pure _ _).1 hC
  have hR := RunBlockOn_vocabulary_eq (V := V) S rho Xb
  have hCone := NamedHonestVotesConeOn_vocabulary_eq (V := V) S rho Hs Xb
    ((Record.Model.vocabulary (V := V)).opening_slot S.hc q - 1) (fun X => ceiling ⪯ X)
  constructor
  · intro h
    exact
      { targetErase := h.targetErase
        targetRun := (hR target).1 h.targetRun
        targetHeight := h.targetHeight
        targetHeightPositive := h.targetHeightPositive
        actionWitnessHonest := h.actionWitnessHonest
        actionCeilingEq := hEq.1 h.actionCeilingEq
        ceilingUpper := fun v hv =>
          (actionCarrierFrom_vocabulary₄₂c S rho v (q - 1) (fun B => B ⪯ ceiling)).2 (h.ceilingUpper v hv)
        ceilingCone := hCone.1 h.ceilingCone
        ceilingRoot := h.ceilingRoot
        ceilingChoice := h.ceilingChoice
        anchorFiltered := h.anchorFiltered
        rootAtProposal := h.rootAtProposal
        hMaxAtProposal := h.hMaxAtProposal }
  · intro h
    exact
      { targetErase := h.targetErase
        targetRun := (hR target).2 h.targetRun
        targetHeight := h.targetHeight
        targetHeightPositive := h.targetHeightPositive
        actionWitnessHonest := h.actionWitnessHonest
        actionCeilingEq := hEq.2 h.actionCeilingEq
        ceilingUpper := fun v hv =>
          (actionCarrierFrom_vocabulary₄₂c S rho v (q - 1) (fun B => B ⪯ ceiling)).1 (h.ceilingUpper v hv)
        ceilingCone := hCone.2 h.ceilingCone
        ceilingRoot := h.ceilingRoot
        ceilingChoice := h.ceilingChoice
        anchorFiltered := h.anchorFiltered
        rootAtProposal := h.rootAtProposal
        hMaxAtProposal := h.hMaxAtProposal }

/-- `Restated.NamedSGProposalLifecycleInputsOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedSGProposalLifecycleInputsOn`. -/
@[record_vocabulary]
theorem NamedSGProposalLifecycleInputsOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (X Xb : Finset V) (r : Round) (s : Slot) (A : Block V) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedSGProposalLifecycleInputsOn (V := V) S rho Hs X Xb r s A P ↔ Restated.NamedSGProposalLifecycleInputsOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs X Xb r s A P :=
  by
  (constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [namedG1At_iff_body_vocabulary₄₂c] at *) <;>
    (try simp only [record_vocabulary, Membership.mem, Set.Mem,
      Singleton.singleton, Set.singleton, setOf, forall_eq,
      vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq'] at *) <;> assumption)

/-- `DecoupledConsensusModel.Sts.GateOffOpeningAdoptionOn` holds exactly when
    `Restated.GateOffOpeningAdoptionOn` holds at the model `Record.Model.vocabulary` for some proposal
    `P`. -/
@[record_vocabulary]
theorem GateOffOpeningAdoptionOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.GateOffOpeningAdoptionOn (V := V) S rho Hs Xb q ↔
      ∃ P : NamedBlock V, Restated.GateOffOpeningAdoptionOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb q P :=
  by
  constructor
  · intro h
    obtain ⟨P, hP⟩ := h.proposal
    have hvotes := h.votes P hP
    have hgenuine := h.genuineConfirmation P hP
    have hcover := h.actionCover P hP
    have hgrade := h.gradeNext P hP
    have hlife := h.lifecycle P hP
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc q) P).1 hP
    clear h hP
    refine ⟨P, ?_⟩
    constructor
    case proposal => exact hp
    all_goals
      ((try simp only [namedGradeFormsAt_iff_body_vocabulary₄₂c] at *);
       (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
         vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
         forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *);
       first
       | assumption
       | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
           forall_apply_eq_imp_iff] at *; assumption))
  · rintro ⟨P, h⟩
    have hP : _root_.DecoupledConsensusModel.Statements.Instantiation.proposedBlockAt S rho
        (S.hc.opening_slot q) = some P :=
      (proposedBlockAt_iff_body_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc q) P).2 h.proposal
    cases h
    constructor
    case proposal => exact ⟨P, hP⟩
    all_goals
      (intro P' hP'
       obtain rfl : P = P' := Option.some.inj (hP.symm.trans hP')
       (try simp only [namedGradeFormsAt_iff_body_vocabulary₄₂c] at *)
       (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
         vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
         forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *)
       first
       | assumption
       | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
           forall_apply_eq_imp_iff] at *; assumption))

/-- `Restated.NamedGateOffOpeningWindowAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedGateOffOpeningWindowAtOn`. -/
@[record_vocabulary]
theorem NamedGateOffOpeningWindowAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (q : Round) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedGateOffOpeningWindowAtOn (V := V) S rho Hs M q P ↔ Restated.NamedGateOffOpeningWindowAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M q P :=
  by
  constructor
  · intro h
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc q) P).1 h.proposal
    cases h
    constructor
    case proposal => exact hp
    all_goals
      ((try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
         vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
         forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *);
       first
       | assumption
       | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
           forall_apply_eq_imp_iff] at *; assumption))
  · intro h
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc q) P).2 h.proposal
    cases h
    constructor
    case proposal => exact hp
    all_goals
      ((try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
         vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
         forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *);
       first
       | assumption
       | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
           forall_apply_eq_imp_iff] at *; assumption))

/-- `Restated.FixedHeightRootOpeningParentRunOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.FixedHeightRootOpeningParentRunOn`. -/
@[record_vocabulary]
theorem FixedHeightRootOpeningParentRunOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.FixedHeightRootOpeningParentRunOn (V := V) S rho Hs q ↔ Restated.FixedHeightRootOpeningParentRunOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q :=
  by
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun w hw B hB => ?_⟩
    · refine (actionCarrierFrom_vocabulary₄₂c S rho v (q - 1) _).2 ?_
      exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc q)
        (fun Q => actionSGBlockAt S rho v (q - 1) ⪯ Q)).2 (h.actionTargetParent v hv)
    · exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc q) (fun Q => B ⪯ Q)).2
        (h.liveG1Parent w hw B ((namedG1At_iff_body_vocabulary₄₂c S rho w q B).2 hB))
  · intro h
    refine ⟨fun v hv => ?_, fun w hw B hB => ?_⟩
    · have h1 := (actionCarrierFrom_vocabulary₄₂c S rho v (q - 1) _).1 (h.actionTargetParent v hv)
      exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc q)
        (fun Q => actionSGBlockAt S rho v (q - 1) ⪯ Q)).1 h1
    · exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc q) (fun Q => B ⪯ Q)).1
        (h.liveG1Parent w hw B ((namedG1At_iff_body_vocabulary₄₂c S rho w q B).1 hB))

/-- `Restated.NamedSGProposalLifecyclePacketOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.NamedSGProposalLifecyclePacketOn`. -/
@[record_vocabulary]
theorem NamedSGProposalLifecyclePacketOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r : Round) (s : Slot) (P : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.NamedSGProposalLifecyclePacketOn (V := V) S rho Hs Xb r s P ↔
      Restated.NamedSGProposalLifecyclePacketOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        (NamedRun.stateBeforeTime S rho (Protocol.confirmation_time S.E (S.hc.opening_slot (r + 1))))
        (NamedRun.readAt S rho (Protocol.confirmation_time S.E (S.hc.opening_slot (r + 1))))
        Hs Xb r s P :=
  by
  constructor
  · intro h
    have h3 := h.actionTargetParent
    have h4 := h.liveG1Parent
    have h7 := h.g0ClearAtAction
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc (r + 1)) P).1 h.proposal
    cases h
    constructor
    case proposal => exact hp
    case actionTargetParent =>
      intro v hv
      refine (actionCarrierFrom_vocabulary₄₂c S rho v r _).2 ?_
      exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc (r + 1))
        (fun Q => actionSGBlockAt S rho v r ⪯ Q)).2 (h3 v hv)
    case liveG1Parent =>
      intro w hw X hX
      exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc (r + 1)) (fun Q => X ⪯ Q)).2
        (h4 w hw X ((namedG1At_iff_body_vocabulary₄₂c S rho w (r + 1) X).2 hX))
    case g0ClearAtAction =>
      intro v hv n hn b hb
      rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq] at hn
      obtain rfl : n = _ := hn
      have h7' := h7 v hv
      simp only [record_vocabulary, returns_pure_eq₄₂c] at hb
      exact hb ▸ h7'
    all_goals
      ((try simp only [record_vocabulary, Membership.mem, Set.Mem,
        Singleton.singleton, Set.singleton, setOf, forall_eq] at *); assumption)
  · intro h
    have h3 := h.actionTargetParent
    have h4 := h.liveG1Parent
    have h7 := h.g0ClearAtAction
    have hp := (proposedBlockAt_iff_body_vocabulary₄₂c S rho
      ((Record.Model.vocabulary (V := V)).opening_slot S.hc (r + 1)) P).2 h.proposal
    cases h
    constructor
    case proposal => exact hp
    case actionTargetParent =>
      intro v hv
      have h1 := (actionCarrierFrom_vocabulary₄₂c S rho v r _).1 (h3 v hv)
      exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc (r + 1))
        (fun Q => actionSGBlockAt S rho v r ⪯ Q)).1 h1
    case liveG1Parent =>
      intro w hw X hX
      exact (proposedParentFrom_vocabulary₄₂c S rho
        ((Record.Model.vocabulary (V := V)).opening_slot S.hc (r + 1)) (fun Q => X ⪯ Q)).1
        (h4 w hw X ((namedG1At_iff_body_vocabulary₄₂c S rho w (r + 1) X).1 hX))
    case g0ClearAtAction =>
      intro v hv
      have hn : actionStoreAt S rho v (r + 1) ∈
          Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
            (NamedRun.stateBeforeTime S rho (S.a (r + 1)) v) (r + 1) := by
        rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]
        exact Set.mem_singleton _
      have h7' := h7 v hv _ hn
      simp only [record_vocabulary, returns_pure_eq₄₂c, forall_eq'] at h7'
      exact h7'
    all_goals
      ((try simp only [record_vocabulary, Membership.mem, Set.Mem,
        Singleton.singleton, Set.singleton, setOf, forall_eq] at *); assumption)

/-- `Restated.ActiveExactHeightProposalRootCarrierAtOn` at the model `Record.Model.vocabulary` agrees
    with `DecoupledConsensusModel.Sts.ActiveExactHeightProposalRootCarrierAtOn`. -/
@[record_vocabulary]
theorem ActiveExactHeightProposalRootCarrierAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (H : Height) (q : Round) (endpoint : Time) (source root : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.ActiveExactHeightProposalRootCarrierAtOn (V := V) S rho Hs Xb H q endpoint source root ↔
      Restated.ActiveExactHeightProposalRootCarrierAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        (NamedRun.readAt S rho endpoint) Hs Xb H q endpoint source root
        (Protocol.onPhaseTick S.E S.hc
          (Record.Model.N.st (M := Record.Model.vocabulary)
            (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).proposal_time S.E
                ((Record.Model.vocabulary (V := V)).opening_slot S.hc q))
              (S.E.proposer ((Record.Model.vocabulary (V := V)).opening_slot S.hc q)))).core.toHealing
          ((Record.Model.vocabulary (V := V)).proposal_time S.E
            ((Record.Model.vocabulary (V := V)).opening_slot S.hc q))
          (Record.Model.N.cache (M := Record.Model.vocabulary)
            (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).proposal_time S.E
                ((Record.Model.vocabulary (V := V)).opening_slot S.hc q))
              (S.E.proposer ((Record.Model.vocabulary (V := V)).opening_slot S.hc q))))) := by
  have hG : _root_.DecoupledConsensusModel.Sts.NamedGradeFormsAtOn (V := V) S rho Hs (q - 1)
        source.erase ↔
      ∀ v ∈ Hs ((Record.Model.vocabulary (V := V)).domain S.E S.hc (q - 1) Phase.g2),
        source.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree Record.Model.vocabulary
            (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).domain S.E S.hc (q - 1) Phase.g2) v) ∧
          ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade Record.Model.vocabulary S.E S.hc
            (Record.Model.N.st (M := Record.Model.vocabulary) (NamedRun.stateBeforeTime S rho
              ((Record.Model.vocabulary (V := V)).domain S.E S.hc (q - 1) Phase.g2) v))
            (q - 1) Phase.g2 source.erase ⇢ b → b = true :=
    NamedGradeFormsAtOn_vocabulary_eq S rho Hs (q - 1) source.erase
  constructor <;> intro h <;> cases h <;> constructor <;>
    first
    | (apply hG.1; assumption)
    | (apply hG.2; assumption)
    | (try simp only [record_vocabulary, Membership.mem, Set.Mem, returns_pure_eq₄₂c, forall_eq',
        confReadAt_vocabulary₄₂c] at *
       assumption)

/-- `Restated.BoundedHeightGradeSourceAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.BoundedHeightGradeSourceAtOn`. -/
@[record_vocabulary]
theorem BoundedHeightGradeSourceAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 start bound : Round) (origin source : Round) (C : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.BoundedHeightGradeSourceAtOn (V := V) S rho Hs Xb r0 start bound origin source C ↔
      Restated.BoundedHeightGradeSourceAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) (fun t => NamedRun.readAt S rho t)
        Hs Xb r0 start bound origin source C :=
  by
  record_vocabulary_struct_iff

/-- `Restated.BoundedHeightGradeOrProgressFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.BoundedHeightGradeOrProgressFromOn`. -/
@[record_vocabulary]
theorem BoundedHeightGradeOrProgressFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 lag : Round) :
    _root_.DecoupledConsensusModel.Sts.BoundedHeightGradeOrProgressFromOn (V := V) S rho Hs Xb r0 lag ↔
      Restated.BoundedHeightGradeOrProgressFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) (fun t => NamedRun.readAt S rho t) Hs Xb r0 lag := by
  simp only [Restated.BoundedHeightGradeOrProgressFromOn,
    _root_.DecoupledConsensusModel.Sts.BoundedHeightGradeOrProgressFromOn,
    Restated.BoundedHeightGradeSourceAtOn_vocabulary_eq]
  exact Iff.rfl

/-- `Restated.GoldfishConeSlotInputsOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.GoldfishConeSlotInputsOn`. -/
@[record_vocabulary]
theorem GoldfishConeSlotInputsOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (s : Slot) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.GoldfishConeSlotInputsOn (V := V) S rho Hs s C ↔ Restated.GoldfishConeSlotInputsOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs s C :=
  by
  record_vocabulary_struct_iff₄₂c

/-- `Restated.RoundCeilingAboveRootAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingAboveRootAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingAboveRootAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingAboveRootAtOn (V := V) S rho Hs q C ↔ Restated.RoundCeilingAboveRootAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q C :=
  by
  record_vocabulary_struct_iff

/-- `Restated.RoundCeilingActiveAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingActiveAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingActiveAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingActiveAtOn (V := V) S rho Hs q C ↔ Restated.RoundCeilingActiveAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q C :=
  by
  record_vocabulary_struct_iff

/-- `Restated.RoundCeilingAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) (C : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingAtOn (V := V) S rho Hs Xb M q C ↔ Restated.RoundCeilingAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb M q C :=
  by
  record_vocabulary_struct_iff₄₂c

/-- `Restated.RoundCeilingNextRootOrderAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingNextRootOrderAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingNextRootOrderAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingNextRootOrderAtOn (V := V) S rho Hs q C ↔ Restated.RoundCeilingNextRootOrderAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q C :=
  by
  record_vocabulary_struct_iff

/-- `Restated.RoundCeilingNextRegimeAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingNextRegimeAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingNextRegimeAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingNextRegimeAtOn (V := V) S rho Hs M q ↔ Restated.RoundCeilingNextRegimeAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M q :=
  by
  record_vocabulary_struct_iff

/-- `Restated.RoundCeilingBoundaryConeAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingBoundaryConeAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingBoundaryConeAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) (C : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingBoundaryConeAtOn (V := V) S rho Hs Xb M q C ↔ Restated.RoundCeilingBoundaryConeAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb M q C :=
  by
  record_vocabulary_struct_iff₄₂c

/-- `Restated.RoundCeilingStepResidualAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingStepResidualAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingStepResidualAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) (Cstar : Block V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingStepResidualAtOn (V := V) S rho Hs Xb M q Cstar ↔ Restated.RoundCeilingStepResidualAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb M q Cstar :=
  by
  record_vocabulary_struct_iff₄₂c

/-- At `Record.Model.vocabulary`, the live confirmed blocks of `v`'s round-`q` action node states,
    staged from its node state before `S.a q`, are its round-`q` opening outputs. -/
private theorem openingOutputFrom_vocabulary₄₂c (S : Setup V) (rho : Run V) (q : Round) (v : V) :
    (fun n : (Record.Model.vocabulary (V := V)).N => n.live_confirmed) ''
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
          (NamedRun.stateBeforeTime S rho (Restated.Vocabulary.Execution.Setup.a Record.Model.vocabulary S q) v) q =
      Restated.Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput Record.Model.vocabulary S
        (Record.Run.ofVocabulary rho) q v := by
  ext B
  simp only [Restated.Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput,
    Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt,
    Restated.Vocabulary.Proofs.HealingSurface.actionReadAt,
    Restated.Vocabulary.Execution.NamedActionReads.actionReadAt,
    Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, ⟨_, rfl, hx⟩, rfl⟩
  · rintro ⟨x, ⟨w, hw, hx⟩, rfl⟩
    obtain rfl : w = _ := hw
    exact ⟨x, hx, rfl⟩

/-- `Restated.roundCeilingFrontierCandidatesOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.roundCeilingFrontierCandidatesOn`. -/
@[record_vocabulary]
theorem roundCeilingFrontierCandidatesOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) (C : NamedBlock V) :
    Restated.roundCeilingFrontierCandidatesOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q C =
      {_root_.DecoupledConsensusModel.Sts.roundCeilingFrontierCandidatesOn (V := V) S rho Hs q C} := by
  ext F
  constructor
  · rintro ⟨out, hout, rfl⟩
    show _ = _
    unfold _root_.DecoupledConsensusModel.Sts.roundCeilingFrontierCandidatesOn
    congr 1
    refine Finset.image_congr fun v hv => ?_
    have h : out v ∈ Restated.Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput
        Record.Model.vocabulary S (Record.Run.ofVocabulary rho) q v := by
      rw [← openingOutputFrom_vocabulary₄₂c]; exact hout v hv
    rw [Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput_vocabulary_eq] at h
    exact h
  · intro hF
    refine ⟨fun v => _root_.DecoupledConsensusModel.Proofs.HealingSurface.roundCeilingOpeningOutput S rho q v,
      fun v _ => ?_, hF⟩
    show _ ∈ (fun n : (Record.Model.vocabulary (V := V)).N => n.live_confirmed) ''
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
          (NamedRun.stateBeforeTime S rho (Restated.Vocabulary.Execution.Setup.a Record.Model.vocabulary S q) v) q
    rw [openingOutputFrom_vocabulary₄₂c, Vocabulary.Proofs.HealingSurface.roundCeilingOpeningOutput_vocabulary_eq]
    rfl

/-- `Restated.RoundCeilingFrontierAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingFrontierAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingFrontierAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (q : Round) (C Cstar : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingFrontierAtOn (V := V) S rho Hs Xb q C Cstar ↔ Restated.RoundCeilingFrontierAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb q C Cstar := by
  constructor <;> intro h <;> cases h <;> constructor <;>
    (try simp only [openingOutputFrom_vocabulary₄₂c] at *) <;>
    (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
      Singleton.singleton, Set.singleton, setOf, forall_eq] at *) <;> assumption

/-- `Restated.RoundCeilingRelayFoldAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.RoundCeilingRelayFoldAtOn`. -/
@[record_vocabulary]
theorem RoundCeilingRelayFoldAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.RoundCeilingRelayFoldAtOn (V := V) S rho Hs q C ↔ Restated.RoundCeilingRelayFoldAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q C :=
  by
  record_vocabulary_struct_iff₄₂c

/-- `Restated.seedRootReadCandidatesOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.seedRootReadCandidatesOn`. -/
@[record_vocabulary]
theorem seedRootReadCandidatesOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) :
    Restated.seedRootReadCandidatesOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q =
      _root_.DecoupledConsensusModel.Sts.seedRootReadCandidatesOn (V := V) S rho Hs q := by
  rfl

/-- `Restated.OpeningCeilingAlignedAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.OpeningCeilingAlignedAtOn`. -/
@[record_vocabulary]
theorem OpeningCeilingAlignedAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.OpeningCeilingAlignedAtOn (V := V) S rho Hs q C ↔ Restated.OpeningCeilingAlignedAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs q C :=
  by
  record_vocabulary_struct_iff

/-- `Restated.DeepestActionCarrierCeilingAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.DeepestActionCarrierCeilingAtOn`. -/
@[record_vocabulary]
theorem DeepestActionCarrierCeilingAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) (C : Block V) :
    _root_.DecoupledConsensusModel.Sts.DeepestActionCarrierCeilingAtOn (V := V) S rho Hs Xb M q C ↔ Restated.DeepestActionCarrierCeilingAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Hs Xb M q C
        (NamedRun.stateBeforeTime S rho (S.a q)) := by
  have hR := RunBlockOn_vocabulary_eq (V := V) S rho Xb
  constructor
  · rintro ⟨⟨v, hv, hC, Wn, hWn, hCW, hrun, hh⟩, ⟨D, hD, hDrun⟩, hprev⟩
    have hn : actionStoreAt S rho v q ∈
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom Record.Model.vocabulary S
          (NamedRun.stateBeforeTime S rho (S.a q) v) q := by
      rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]
      exact Set.mem_singleton _
    refine ⟨⟨v, hv, actionStoreAt S rho v q, hn,
        ⟨_, (Record.returns_pure _ _).2 rfl, (Record.returns_pure _ _).2 hC.symm⟩,
        Wn, hWn, hCW, (hR Wn).1 hrun, hh⟩,
      ⟨D, hD, (hR D).1 hDrun⟩, fun v hv => ?_⟩
    exact (actionCarrierFrom_vocabulary₄₂c S rho v q (fun B => B ⪯ C)).2 (hprev v hv)
  · rintro ⟨⟨v, hv, n, hn, ⟨A2, hA2, hC⟩, Wn, hWn, hCW, hrun, hh⟩, ⟨D, hD, hDrun⟩, hprev⟩
    rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq] at hn
    obtain rfl : n = _ := hn
    obtain rfl := (Record.returns_pure _ _).1 hA2
    refine ⟨⟨v, hv, ((Record.returns_pure _ _).1 hC).symm, Wn, hWn, hCW, (hR Wn).2 hrun, hh⟩,
      ⟨D, hD, (hR D).2 hDrun⟩, fun v hv => ?_⟩
    exact (actionCarrierFrom_vocabulary₄₂c S rho v q (fun B => B ⪯ C)).1 (hprev v hv)

/-- `Restated.SeedRoundGradedAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedRoundGradedAtOn`. -/
@[record_vocabulary]
theorem SeedRoundGradedAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedRoundGradedAtOn (V := V) S rho Hs q ↔ Restated.SeedRoundGradedAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs q :=
  by
  record_vocabulary_struct_iff₄₂c

/-- `Restated.SeedRoundBandGradeAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedRoundBandGradeAtOn`. -/
@[record_vocabulary]
theorem SeedRoundBandGradeAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedRoundBandGradeAtOn (V := V) S rho Hs Xb M q ↔ Restated.SeedRoundBandGradeAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb M q := by
  record_vocabulary_iff [Restated.SeedRoundBandGradeAtOn, _root_.DecoupledConsensusModel.Sts.SeedRoundBandGradeAtOn]

/-- `Restated.SeedBandCarrierCoverAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedBandCarrierCoverAtOn`. -/
@[record_vocabulary]
theorem SeedBandCarrierCoverAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedBandCarrierCoverAtOn (V := V) S rho Hs Xb M q ↔ Restated.SeedBandCarrierCoverAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i) Hs Xb M q
        (NamedRun.stateBeforeTime S rho (S.a q)) := by
  record_vocabulary_iff [Restated.SeedBandCarrierCoverAtOn, _root_.DecoupledConsensusModel.Sts.SeedBandCarrierCoverAtOn]

/-- `Restated.SeedRoundDischargeAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedRoundDischargeAtOn`. -/
@[record_vocabulary]
theorem SeedRoundDischargeAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (c : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedRoundDischargeAtOn (V := V) S rho Hs Xb M c ↔ Restated.SeedRoundDischargeAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb M c :=
  by
  record_vocabulary_struct_iff₄₂c

/-- `Restated.SeedDischargeFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedDischargeFromOn`. -/
@[record_vocabulary]
theorem SeedDischargeFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedDischargeFromOn (V := V) S rho Hs Xb r0 ↔ Restated.SeedDischargeFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        Hs Xb r0 := by
  record_vocabulary_iff [Restated.SeedDischargeFromOn, _root_.DecoupledConsensusModel.Sts.SeedDischargeFromOn]

/-- `Restated.SeedBandReachFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedBandReachFromOn`. -/
@[record_vocabulary]
theorem SeedBandReachFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedBandReachFromOn (V := V) S rho Hs Xb r0 ↔ Restated.SeedBandReachFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb r0 := by
  unfold Restated.SeedBandReachFromOn _root_.DecoupledConsensusModel.Sts.SeedBandReachFromOn
  constructor <;> intro h <;>
    (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
      Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
      vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
      forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *) <;>
    first
    | assumption
    | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
        forall_apply_eq_imp_iff] at *; assumption)

/-- `Restated.SeedRawG2FromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedRawG2FromOn`. -/
@[record_vocabulary]
theorem SeedRawG2FromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r0 : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedRawG2FromOn (V := V) S rho Hs r0 ↔ Restated.SeedRawG2FromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs r0 := by
  record_vocabulary_iff [Restated.SeedRawG2FromOn, _root_.DecoupledConsensusModel.Sts.SeedRawG2FromOn]

/-- `Restated.SeedAnchorCompatFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedAnchorCompatFromOn`. -/
@[record_vocabulary]
theorem SeedAnchorCompatFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r0 : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedAnchorCompatFromOn (V := V) S rho Hs r0 ↔ Restated.SeedAnchorCompatFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs r0 := by
  unfold Restated.SeedAnchorCompatFromOn _root_.DecoupledConsensusModel.Sts.SeedAnchorCompatFromOn
  constructor <;> intro h <;>
    (try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
      Singleton.singleton, Set.singleton, setOf, forall_eq, vocabulary_onPhaseTick₄₂c,
      vocabulary_get_sg_root_with₄₂c, returns_pure_eq₄₂c, forall_eq',
      forall_apply_eq_imp_iff, confReadAt_vocabulary₄₂c] at *) <;>
    first
    | assumption
    | (simp only [Record.Model.vocabulary, returns_pure_eq₄₂c, forall_eq, forall_eq',
        forall_apply_eq_imp_iff] at *; assumption)

/-- `Restated.SeedRoundRegimeAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedRoundRegimeAtOn`. -/
@[record_vocabulary]
theorem SeedRoundRegimeAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedRoundRegimeAtOn (V := V) S rho Hs M q ↔ Restated.SeedRoundRegimeAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun t => NamedRun.stateBeforeTime S rho t) Hs M q :=
  by
  record_vocabulary_struct_iff

/-- `Restated.SeedBoundaryAdoptionAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedBoundaryAdoptionAtOn`. -/
@[record_vocabulary]
theorem SeedBoundaryAdoptionAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (q : Round) :
    _root_.DecoupledConsensusModel.Sts.SeedBoundaryAdoptionAtOn (V := V) S rho Hs Xb M q ↔ Restated.SeedBoundaryAdoptionAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) Hs Xb M q (NamedRun.stateBeforeTime S rho (S.a q)) :=
  by
  constructor
  · intro h
    obtain ⟨C, hCrun, hWn, hcarriers, hheads⟩ := h.entry
    have hthin := h.headThin
    clear h
    refine ⟨?_, C, ?_, ?_, fun v hv =>
      (actionCarrierFrom_vocabulary₄₂c S rho v q (fun B => B ⪯ C.erase)).2 (hcarriers v hv), ?_⟩
    all_goals
      ((try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq] at *);
       assumption)
  · intro h
    obtain ⟨C, hCrun, hWn, hcarriers, hheads⟩ := h.entry
    have hthin := h.headThin
    clear h
    refine ⟨?_, C, ?_, ?_, fun v hv =>
      (actionCarrierFrom_vocabulary₄₂c S rho v q (fun B => B ⪯ C.erase)).1 (hcarriers v hv), ?_⟩
    all_goals
      ((try simp only [record_vocabulary, Record.stateBeforeOf_vocabulary, Membership.mem, Set.Mem,
         Singleton.singleton, Set.singleton, setOf, forall_eq] at *);
       assumption)

/-- `Restated.HeightProgressSeedOutcomeOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HeightProgressSeedOutcomeOn`. -/
@[record_vocabulary]
theorem HeightProgressSeedOutcomeOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (M : Height) (base endpointRound : Round) (delayExtra : Nat := 0) :
    _root_.DecoupledConsensusModel.Sts.HeightProgressSeedOutcomeOn (V := V) S rho Hs Xb M base endpointRound delayExtra ↔
      Restated.HeightProgressSeedOutcomeOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) (fun t => NamedRun.readAt S rho t)
        Hs Xb M base endpointRound delayExtra := by
  unfold Restated.HeightProgressSeedOutcomeOn
    _root_.DecoupledConsensusModel.Sts.HeightProgressSeedOutcomeOn
  simp only [proposedBlockAt_iff_body_vocabulary₄₂c, namedGradeFormsAt_iff_body_vocabulary₄₂c]
  record_vocabulary_iff [_root_.DecoupledConsensusModel.Sts.honestHMaxAtOn, exists_eq_left]

/-- `Restated.HeightProgressSeedFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.HeightProgressSeedFromOn`. -/
@[record_vocabulary]
theorem HeightProgressSeedFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 gap : Round) (delayExtra : Nat := 0) :
    _root_.DecoupledConsensusModel.Sts.HeightProgressSeedFromOn (V := V) S rho Hs Xb r0 gap delayExtra ↔
      Restated.HeightProgressSeedFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) (fun i => NamedRun.stateBefore S rho i)
        (fun t => NamedRun.stateBeforeTime S rho t) (fun t => NamedRun.readAt S rho t)
        Hs Xb r0 gap delayExtra := by
  record_vocabulary_iff [Restated.HeightProgressSeedFromOn,
    _root_.DecoupledConsensusModel.Sts.HeightProgressSeedFromOn,
    _root_.DecoupledConsensusModel.Sts.honestHMaxAtOn, forall_eq']

/-- `Restated.SeedPredPromotionInputsAtOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedPredPromotionInputsAtOn`. -/
@[record_vocabulary]
theorem SeedPredPromotionInputsAtOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height) (q q' : Round) (B B' : NamedBlock V) :
    _root_.DecoupledConsensusModel.Sts.SeedPredPromotionInputsAtOn (V := V) S rho Hs M q q' B B' ↔ Restated.SeedPredPromotionInputsAtOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) Hs M q q' B B'
        (NamedRun.stateBeforeTime S rho (S.a (q' - 1))) :=
  by
  record_vocabulary_struct_iff

/-- `Restated.SeedPredPromotionInputsOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedPredPromotionInputsOn`. -/
@[record_vocabulary]
theorem SeedPredPromotionInputsOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 : Round) (delayExtra : Nat := 0) :
    _root_.DecoupledConsensusModel.Sts.SeedPredPromotionInputsOn (V := V) S rho Hs Xb r0 delayExtra ↔ Restated.SeedPredPromotionInputsOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t) Hs Xb r0 delayExtra := by
  unfold Restated.SeedPredPromotionInputsOn _root_.DecoupledConsensusModel.Sts.SeedPredPromotionInputsOn
  simp only [namedGradeFormsAt_iff_body_vocabulary₄₂c,
    _root_.DecoupledConsensusModel.Proofs.HealingSurface.FinalityFilterRetainedAtRead]
  record_vocabulary_iff [forall_eq]

/-- `Restated.SeedPredCloserFromOn` at the model `Record.Model.vocabulary` agrees with
    `DecoupledConsensusModel.Sts.SeedPredCloserFromOn`. -/
@[record_vocabulary]
theorem SeedPredCloserFromOn_vocabulary_eq (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V) (r0 gap : Round) (delayExtra : Nat := 0) :
    _root_.DecoupledConsensusModel.Sts.SeedPredCloserFromOn (V := V) S rho Hs Xb r0 gap delayExtra ↔ Restated.SeedPredCloserFromOn (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) (fun t => NamedRun.stateBeforeTime S rho t)
        (fun t => NamedRun.readAt S rho t) Hs Xb r0 gap delayExtra := by
  record_vocabulary_iff [Restated.SeedPredCloserFromOn, _root_.DecoupledConsensusModel.Sts.SeedPredCloserFromOn,
    _root_.DecoupledConsensusModel.Sts.honestHMaxAtOn, forall_eq']

end

end DecoupledConsensusModel.Sts.Restated
