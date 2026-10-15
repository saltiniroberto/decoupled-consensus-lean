import Proofs.Claims.Spec2Claims.Claim13beRoute3_42b

/-!
# Per-instant honest-set definitions, continued

The `On` forms of the fixed-height roots, the lifecycles, the round ceilings and the seed: each
validator a definition reads is taken from the family `Hs : Int → Finset V` at the instant of its
read, and run blocks are read through the set `Xb`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Fixed-height roots and carriers -/

/-- The store `st` is at frontier `H` with justification at `H − 1`, its justified target is the one
    certified target at height `H − 1`, and that target is a run block read through `Xb`. -/
structure FixedHeightJustificationRootOn (S : Setup V) (rho : Run V) (Xb : Finset V)
    (st : Store V) (H : Height) : Prop where
  frontier : st.h_max = H
  justificationHeight : st.h_j = H - 1
  gate : st.h_max = st.h_j + 1
  certificate : CertificateOn S rho Xb (H - 1) st.J.root
  uniqueAtHeight : ∀ T : BlockId, CertificateOn S rho Xb (H - 1) T → T = st.J.root
  targetBlock : RunBlockOfOn S rho Xb st.J

/-- `FixedHeightJustificationRootOn` holds of `st`, and its justified target is incompatible with
    `P`. -/
structure FixedHeightRootTargetOn (S : Setup V) (rho : Run V) (Xb : Finset V) (st : Store V)
    (P : Block V) (H : Height) : Prop where
  frontier : st.h_max = H
  justificationHeight : st.h_j = H - 1
  gate : st.h_max = st.h_j + 1
  certificate : CertificateOn S rho Xb (H - 1) st.J.root
  uniqueAtHeight : ∀ T : BlockId, CertificateOn S rho Xb (H - 1) T → T = st.J.root
  targetBlock : RunBlockOfOn S rho Xb st.J
  incompatible : st.J.compatible P = false

/-- `w` is in `Hs read`, `read` is in the horizon, `w`'s store just before `read` holds a run block
    carrying its justification, and that store satisfies `FixedHeightJustificationRootOn` at `H`. -/
structure FixedHeightJustificationRootAtReadOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (H : Height) (w : V) (read : Time) : Prop where
  readerHonest : w ∈ Hs read
  readInHorizon : read ≤ rho.horizon
  carrierExists : ∃ D ∈ (Run.storeBeforeTime S rho w read).bodies, RunBlockOn S rho Xb D ∧
    NamedJustifiedAt S.E S.cfg D (Run.storeBeforeTime S rho w read).J
      (Run.storeBeforeTime S rho w read).h_j
  targetHeightPositive : 0 < H - 1
  fixedTarget : FixedHeightJustificationRootOn S rho Xb (Run.storeBeforeTime S rho w read).core H

/-- `FixedHeightJustificationRootAtReadOn` holds for `w` at `read`, with a protected run block `P`
    of height at least `H` in `w`'s tree that the finality root interferes with. -/
structure FixedHeightRootInterferenceAtReadOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (H : Height) (w : V) (read : Time) (P : Block V) : Prop where
  readerHonest : w ∈ Hs read
  readInHorizon : read ≤ rho.horizon
  protectedProcessed : P ∈ (Run.storeBeforeTime S rho w read).T
  protectedHeight : ∃ Pn : NamedBlock V, Pn.erase = P ∧ RunBlockOn S rho Xb Pn ∧
    H ≤ (derive_named S.E S.cfg Pn).h
  interference : FGRootInterferenceAt (Run.storeBeforeTime S rho w read) P
  carrierExists : ∃ D ∈ (Run.storeBeforeTime S rho w read).bodies, RunBlockOn S rho Xb D ∧
    NamedJustifiedAt S.E S.cfg D (Run.storeBeforeTime S rho w read).J
      (Run.storeBeforeTime S rho w read).h_j
  targetHeightPositive : 0 < H - 1
  fixedTarget : FixedHeightRootTargetOn S rho Xb (Run.storeBeforeTime S rho w read).core P H

/-- `holder` is in `Hs t`, holds `carrier` in its tree at `t`, and `carrier` erases a run block
    (read through `Xb`) at height `H`. -/
structure HonestHMaxCarrierAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (t : Time) (H : Height) (holder : V) (carrier : Block V) : Prop where
  holderHonest : holder ∈ Hs t
  processed : carrier ∈ (Run.storeAt S rho holder t).T
  namedWitness : ∃ D : NamedBlock V, D.erase = carrier ∧ RunBlockOn S rho Xb D ∧
    (derive_named S.E S.cfg D).h = H

/-- `target` erases the fixed store's justified block, is a run block read through `Xb` at height
    `H − 1`, and is the finality root of the store `pre`, which is at frontier `H`. -/
structure FixedRootPreparedTargetDataOn (S : Setup V) (rho : Run V) (Xb : Finset V) (H : Height)
    (fixed pre : NamedStore V) (target : NamedBlock V) : Prop where
  targetErase : target.erase = fixed.J
  targetRun : RunBlockOn S rho Xb target
  targetHeight : (derive_named S.E S.cfg target).h = H - 1
  targetHeightPositive : 0 < H - 1
  rootAtProposal : get_fg_root pre.toHealing.toFG = target.erase
  hMaxAtProposal : pre.h_max = H

/-- A candidate for the parent of round `q`'s opening proposal over a fixed-height root: the target
    and its height, the round-`(q − 1)` action carriers of `Hs (S.a (q − 1))` bounded by `ceiling`,
    the honest votes before round `q`'s opening slot, and the finality root of `pre`. -/
structure FixedRootPreparedParentCandidateOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (H : Height) (q : Round) (w : V) (read : Time) (A : Block V)
    (target : NamedBlock V) (ceiling actionCeiling : Block V) (actionWitness : V)
    (fixed pre : NamedStore V) (source : Store V) : Prop where
  targetErase : target.erase = fixed.J
  targetRun : RunBlockOn S rho Xb target
  targetHeight : (derive_named S.E S.cfg target).h = H - 1
  targetHeightPositive : 0 < H - 1
  actionWitnessHonest : actionWitness ∈ Hs (S.a (q - 1))
  actionCeilingEq : actionCeiling = actionSGBlockAt S rho actionWitness (q - 1)
  ceilingUpper : ∀ v ∈ Hs (S.a (q - 1)), actionSGBlockAt S rho v (q - 1) ⪯ ceiling
  ceilingCone : NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot q - 1) fun X => ceiling ⪯ X
  ceilingRoot : get_fg_root pre.toHealing.toFG ⪯ ceiling
  ceilingChoice : ceiling = A ∨ ceiling = actionCeiling
  anchorFiltered : A ∈ get_filtered_block_tree source.toHealing.toFG
  rootAtProposal : get_fg_root pre.toHealing.toFG = target.erase
  hMaxAtProposal : pre.h_max = H

/-! ## Lifecycles -/

/-- Round `r`'s opening proposal `P`: proposed by a member of the set at its slot's confirmation
    instant, a run block read through `Xb`, the live-confirmed block of every member of
    `Hs (S.a r)`, covering their action carriers, and graded at round `r + 1`. -/
structure NamedRawOpeningLifecycleAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (P : NamedBlock V) : Prop where
  roundPositive : 0 < r
  proposal : Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot r) = some P
  proposerHonest : S.E.proposer (S.hc.opening_slot r) ∈
    Hs (confirmation_time S.E (S.hc.opening_slot r))
  proposalInHorizon : proposal_time S.E (S.hc.opening_slot r) ≤ rho.horizon
  runBlock : blockInRunOn S rho Xb P
  liveConfirmed : ∀ v ∈ Hs (S.a r), (actionReadAt S rho v r).st.core.live_confirmed = P.erase
  actionCover : ActionCarriersCoverOn S rho Hs r P.erase
  gradeNext : NamedGradeFormsAtOn S rho Hs (r + 1) P.erase

/-- The lifecycle of round `r + 1`'s opening proposal `P` from slot `s`: the round-`r` carriers at
    `S.a r`, the grade-1 readers at round `r + 1`'s grade-1 domain instant, the confirmers at the
    opening slot's confirmation instant and the action readers at `S.a (r + 1)`, each validator
    taken from `Hs` at the instant of its read. -/
structure NamedSGProposalLifecyclePacketOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r : Round) (s : Slot) (P : NamedBlock V) : Prop where
  openingSlot : s + 1 = S.hc.opening_slot (r + 1)
  proposal : Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot (r + 1)) = some P
  actionTargetParent : ∀ v ∈ Hs (S.a r),
    actionSGBlockAt S rho v r ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot (r + 1))
  liveG1Parent : ∀ w ∈ Hs (domain S.E S.hc (r + 1) Phase.g1), ∀ X : Block V,
    namedG1At S rho w (r + 1) X →
      X ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot (r + 1))
  honestVotes : NamedHonestVotesNameOn S rho Hs (S.hc.opening_slot (r + 1)) P.erase
  genuineConfirmation : ∀ v ∈ Hs (confirmation_time S.E (S.hc.opening_slot (r + 1))),
    GenuineConfirmationAt S rho v (S.hc.opening_slot (r + 1)) ∧
      (Run.storeAt S rho v (confirmation_time S.E (S.hc.opening_slot (r + 1)))).live_confirmed =
        P.erase
  g0ClearAtAction : ∀ v ∈ Hs (S.a (r + 1)),
    PhaseGrades.nodeClear S (actionReadAt S rho v (r + 1)) (r + 1) P.erase = true
  lifecycle : NamedRawOpeningLifecycleAtOn S rho Hs Xb (r + 1) P

/-- The inputs of the lifecycle of round `r + 1`'s opening proposal `P` from slot `s`, each
    validator taken from `Hs` at the instant of its read; `X` is a set with no instant. -/
structure NamedSGProposalLifecycleInputsOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (X Xb : Finset V) (r : Round) (s : Slot) (A : Block V) (P : NamedBlock V) : Prop where
  openingSlot : s + 1 = S.hc.opening_slot (r + 1)
  proposal : Statements.Instantiation.proposedBlockAt S rho (s + 1) = some P
  postPreviousAction : S.E.t_GST ≤ S.a r
  postProposalSnapshot : S.E.t_GST ≤ proposal_time S.E s
  previousSupportInHorizon : support_cutoff S.E s ≤ rho.horizon
  actionInHorizon : S.a (r + 1) ≤ rho.horizon
  nextCutoffInHorizon : domain S.E S.hc (r + 1 + 1) Phase.g2 ≤ rho.horizon
  canonical : NamedSGTargetConeCanonicalityOn S rho Hs Xb r s
  concentration : NamedG1ConcentrationOn S rho Hs Xb r s
  proposerHonest : S.E.proposer (s + 1) ∈ Hs (confirmation_time S.E (s + 1))
  proposalAnchor :
    PhaseGrades.nodeAnchor S (Statements.Instantiation.proposerReadAt S rho (s + 1)) (r + 1) = A
  proposalAnchorG1 : PhaseGrades.storeGrade S.E S.hc
    (Statements.Instantiation.proposerReadAt S rho (s + 1)).st (r + 1) Phase.g1 A = true
  actionTargetParent : ∀ v ∈ Hs (S.a r),
    actionSGBlockAt S rho v r ⪯ Proofs.HealingSurface.proposedParent S rho (s + 1)
  liveG1Parent : ∀ w ∈ Hs (domain S.E S.hc (r + 1) Phase.g1), ∀ B : Block V,
    namedG1At S rho w (r + 1) B → B ⪯ Proofs.HealingSurface.proposedParent S rho (s + 1)
  frozenVote : ∀ v ∈ Hs (vote_time S.E (s + 1)), v ∈ S.E.committee (s + 1) →
    NamedSGOpeningFrozenVoteAt S rho s A v P
  confirmationRead : ∀ v ∈ Hs (confirmation_time S.E (s + 1)),
    NamedSGOpeningConfirmationRead S rho (s + 1) v P
  actionBatchAligned : ∀ v ∈ Hs (S.a (r + 1)),
    let n := actionReadAt S rho v (r + 1)
    PhaseGrades.BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F X (r + 1)
      (PhaseGrades.allPhasesCutoff S.E S.hc (r + 1)) P.erase
  actionRootPreceq : ∀ v ∈ Hs (S.a (r + 1)),
    let n := actionReadAt S rho v (r + 1)
    get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc n.st.core.toHealing (r + 1) ⪯
      P.erase
  nextActive : ∀ v ∈ Hs (domain S.E S.hc (r + 1 + 1) Phase.g2),
    P.erase ∈ PhaseGrades.filteredTree (PhaseGrades.readAt S rho (domain S.E S.hc (r + 1 + 1) Phase.g2) v)

/-- Round `q`'s opening proposal exists, and the voters of its slot at the vote instant, its
    confirmers at the confirmation instant, the action carriers and the next grade readers all
    follow it. -/
structure GateOffOpeningAdoptionOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (q : Round) : Prop where
  proposal : ∃ P : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P
  votes : ∀ P : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot q) fun X => P.erase ⪯ X
  genuineConfirmation : ∀ P : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      ∀ v ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)),
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (NamedRecoveryRead.confirmationInputRead S rho v (S.hc.opening_slot q)).cache)
          S.E S.hc (confStore S rho v (S.hc.opening_slot q)) (S.hc.opening_slot q) P.erase
  actionCover : ∀ P : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      ActionCarriersCoverOn S rho Hs q P.erase
  gradeNext : ∀ P : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      NamedGradeFormsAtOn S rho Hs (q + 1) P.erase
  lifecycle : ∀ P : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      NamedRawOpeningLifecycleAtOn S rho Hs Xb q P

/-- The window around round `q`'s opening proposal `P`: post-GST, in the horizon, and every
    proposer, voter, confirmer and next action reader, taken from `Hs` at the instant of its read,
    at frontier `M` with `h_j + 2 ≤ M` and holding `P`. -/
structure NamedGateOffOpeningWindowAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (M : Height) (q : Round) (P : NamedBlock V) : Prop where
  proposal : Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P
  roundPositive : 0 < q
  postPreviousAction : S.E.t_GST ≤ S.a (q - 1)
  postFrozenSnapshot : S.E.t_GST ≤ proposal_time S.E (S.hc.opening_slot q - 1)
  postOpeningVote : S.E.t_GST ≤ vote_time S.E (S.hc.opening_slot q)
  previousCutoffInHorizon : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon
  nextActionInHorizon : S.a (q + 1) ≤ rho.horizon
  parentHeight : M - 1 ≤ (derive_named S.E S.cfg P.parent).h
  proposerFrontier : (proposerDutyStore S rho (S.hc.opening_slot q)).h_max = M
  proposerGateOff : (proposerDutyStore S rho (S.hc.opening_slot q)).h_j + 2 ≤ M
  voteFrontier : ∀ v ∈ Hs (vote_time S.E (S.hc.opening_slot q)),
    (voteDutyStore S rho v (S.hc.opening_slot q)).h_max = M
  voteGateOff : ∀ v ∈ Hs (vote_time S.E (S.hc.opening_slot q)),
    (voteDutyStore S rho v (S.hc.opening_slot q)).h_j + 2 ≤ M
  proposalAtVote : ∀ v ∈ Hs (vote_time S.E (S.hc.opening_slot q)),
    P.erase ∈ (voteDutyStore S rho v (S.hc.opening_slot q)).T
  confirmationFrontier : ∀ v ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)),
    (confStore S rho v (S.hc.opening_slot q)).h_max = M
  confirmationGateOff : ∀ v ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)),
    (confStore S rho v (S.hc.opening_slot q)).h_j + 2 ≤ M
  proposalAtConfirmation : ∀ v ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)),
    P.erase ∈ (confStore S rho v (S.hc.opening_slot q)).T
  nextFrontier : ∀ v ∈ Hs (S.a (q + 1)), (healStoreAt S rho v (q + 1)).h_max = M
  nextGateOff : ∀ v ∈ Hs (S.a (q + 1)), (healStoreAt S rho v (q + 1)).h_j + 2 ≤ M
  proposalAtNext : ∀ v ∈ Hs (S.a (q + 1)), P.erase ∈ (healStoreAt S rho v (q + 1)).T

/-- The round-`(q − 1)` action carrier of every member of `Hs (S.a (q − 1))`, and every grade-1
    block of every member of `Hs (domain q .g1)`, is an ancestor of the parent of round `q`'s
    opening proposal. -/
structure FixedHeightRootOpeningParentRunOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (q : Round) : Prop where
  actionTargetParent : ∀ v ∈ Hs (S.a (q - 1)),
    actionSGBlockAt S rho v (q - 1) ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q)
  liveG1Parent : ∀ w ∈ Hs (domain S.E S.hc q Phase.g1), ∀ B : Block V, namedG1At S rho w q B →
    B ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q)

/-- Round `q`'s opening proposer holds a run block `source` at exact height `H` and its finality
    root `root` at the same height, with `source` a strict ancestor of `root`, each validator taken
    from `Hs` at the instant of its read and run blocks read through `Xb`. -/
structure ActiveExactHeightProposalRootCarrierAtOn (S : Setup V) (rho : Run V)
    (Hs : Int → Finset V) (Xb : Finset V) (H : Height) (q : Round) (endpoint : Time)
    (source root : NamedBlock V) : Prop where
  proposerCarrier : ProposerCarrierAtOn S Hs q
  proposerHonest : S.E.proposer (S.hc.opening_slot q) ∈
    Hs (confirmation_time S.E (S.hc.opening_slot q))
  proposalRead_le_action : proposal_time S.E (S.hc.opening_slot q) ≤ S.a q
  action_le_endpoint : S.a q ≤ endpoint
  endpointInHorizon : endpoint ≤ rho.horizon
  endpointCap : honestHMaxAtOn S rho Hs endpoint ≤ H
  gradeFormsPrev : NamedGradeFormsAtOn S rho Hs (q - 1) source.erase
  sourceActiveAtAction : ∀ w ∈ Hs (S.a q),
    source.erase ∈ get_filtered_block_tree (healStoreAt S rho w q).toFG
  sourceProcessed : source ∈ (Run.storeBeforeTime S rho (S.E.proposer (S.hc.opening_slot q))
    (proposal_time S.E (S.hc.opening_slot q))).bodies
  sourceRunBlock : RunBlockOn S rho Xb source
  sourceExactHeight : (derive_named S.E S.cfg source).h = H
  sourceNotActive : source.erase ∉
    PhaseGrades.filteredTree (Statements.Instantiation.proposerReadAt S rho (S.hc.opening_slot q))
  root_eq : root.erase = get_fg_root
    (Statements.Instantiation.proposerReadAt S rho (S.hc.opening_slot q)).st.core.toHealing.toFG
  sourceStrictRoot : source.erase ≺ root.erase
  rootActive : root.erase ∈
    PhaseGrades.filteredTree (Statements.Instantiation.proposerReadAt S rho (S.hc.opening_slot q))
  rootProcessed : root ∈ (Run.storeBeforeTime S rho (S.E.proposer (S.hc.opening_slot q))
    (proposal_time S.E (S.hc.opening_slot q))).bodies
  rootRunBlock : RunBlockOn S rho Xb root
  rootExactHeight : (derive_named S.E S.cfg root).h = H
  rootExactTarget : (derive_named S.E S.cfg root).T_h.root = (derive_named S.E S.cfg source).T_h.root
  rootPreceqProposedParent :
    root.erase ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q)

/-- An opening lifecycle at round `origin` after `start`, whose proposal `C` is graded 2 at round
    `source ≤ bound`, has height greater than the maximum over `Hs` at `S.a start`, is justifiable,
    and has no height pair at its height emitted before round `origin`'s action. -/
structure BoundedHeightGradeSourceAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r0 start bound : Round) (origin source : Round) (C : NamedBlock V) : Prop where
  startLtOrigin : start < origin
  originLtSource : origin < source
  sourceUpper : source ≤ bound
  lifecycle : NamedRawOpeningLifecycleAtOn S rho Hs Xb origin C
  originAfterBoundary : healingBoundaryTime S r0 < proposal_time S.E (S.hc.opening_slot origin)
  grade : NamedGradeFormsAtOn S rho Hs source C.erase
  sourceAbove : honestHMaxAtOn S rho Hs (S.a start) < (derive_named S.E S.cfg C).h
  sourceJustifiable : (derive_named S.E S.cfg C).nj = false
  originFresh : NoLocalHeightPairBeforeOn S rho Hs (strictEventIndex rho (S.a origin))
    (derive_named S.E S.cfg C).h

/-- `lag` is positive, and every start from `r0` whose `lag` rounds end in the horizon has a
    `BoundedHeightGradeSourceAtOn` source or sees the maximum over `Hs` increase by the end of those
    rounds. -/
def BoundedHeightGradeOrProgressFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (r0 lag : Round) : Prop :=
  0 < lag ∧ ∀ start : Round, r0 ≤ start → S.a (start + lag) ≤ rho.horizon →
    (∃ (origin : Round) (source : Round) (C : NamedBlock V),
        BoundedHeightGradeSourceAtOn S rho Hs Xb r0 start (start + lag) origin source C) ∨
      honestHMaxAtOn S rho Hs (S.a start) < honestHMaxAtOn S rho Hs (S.a (start + lag))

/-! ## Round ceilings -/

/-- Every member of `Hs (vote_time (s + 1))` has the vote inputs of the cone at `C`, and every
    member of `Hs (confirmation_time s)` has its confirmation inputs. -/
structure GoldfishConeSlotInputsOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (s : Slot)
    (C : Block V) : Prop where
  vote : ∀ w ∈ Hs (vote_time S.E (s + 1)), GoldfishConeVoteInputs S rho s C w
  confirmation : ∀ w ∈ Hs (confirmation_time S.E s), GoldfishConeConfirmationInputs S rho s C w

/-- At every read of round `q`, the reader's finality root is an ancestor of `C`, each reader taken
    from `Hs` at the instant of its read. -/
structure RoundCeilingAboveRootAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
    ∀ w ∈ Hs (vote_time S.E d), get_fg_root (voteDutyStore S rho w d).toHealing.toFG ⪯ C
  confirmation : ∀ s : Slot, S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
    ∀ w ∈ Hs (confirmation_time S.E s), confRoot (confStore S rho w s) ⪯ C
  action : ∀ w ∈ Hs (S.a q), get_fg_root (healStoreAt S rho w q).toFG ⪯ C
  proposer : S.E.proposer (S.hc.opening_slot q) ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)) →
    get_fg_root (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG ⪯ C

/-- At every read of round `q`, `C` is in the reader's filtered tree, each reader taken from `Hs` at
    the instant of its read. -/
structure RoundCeilingActiveAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round)
    (C : Block V) : Prop where
  voteDuty : ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
    ∀ w ∈ Hs (vote_time S.E d), C ∈ get_filtered_block_tree (voteDutyStore S rho w d).toHealing.toFG
  confirmation : ∀ s : Slot, S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
    ∀ w ∈ Hs (confirmation_time S.E s), C ∈ confTree (confStore S rho w s)
  action : ∀ w ∈ Hs (S.a q), C ∈ get_filtered_block_tree (healStoreAt S rho w q).toFG
  proposer : S.E.proposer (S.hc.opening_slot q) ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)) →
    C ∈ get_filtered_block_tree (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG

/-- `C` is a ceiling of round `q` at height `M`: its conditions on the vote duties, confirmations,
    action reads, previous carriers and opening proposer of round `q`, each validator taken from
    `Hs` at the instant of its read and run blocks read through `Xb`. -/
structure RoundCeilingAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (M : Height) (q : Round) (C : NamedBlock V) : Prop where
  roundPositive : 0 < q
  run : RunBlockOn S rho Xb C
  boundaryThinHead : ThinHonestHeadAtOn S rho Hs Xb M (S.hc.opening_slot q - 1) C.erase
  aboveRoot : RoundCeilingAboveRootAtOn S rho Hs q C.erase
  active : RoundCeilingActiveAtOn S rho Hs q C.erase
  postPreviousVote : S.E.t_GST ≤ vote_time S.E (S.hc.opening_slot q - 1)
  previousConfirmationInHorizon : confirmation_time S.E (S.hc.opening_slot q - 1) ≤ rho.horizon
  postOpeningProposal : S.E.t_GST ≤ proposal_time S.E (S.hc.opening_slot q)
  postOpeningVote : S.E.t_GST ≤ vote_time S.E (S.hc.opening_slot q)
  roundConfirmationInHorizon : confirmation_time S.E (seedRoundLastSlot S q - 1) ≤ rho.horizon
  lastVotes : NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot q - 1) fun X => C.erase ⪯ X
  openingStepInputs : ∀ w ∈ Hs (vote_time S.E (S.hc.opening_slot q - 1 + 1)),
    GoldfishConeVoteInputs S rho (S.hc.opening_slot q - 1) C.erase w
  roundInputs : ∀ s : Slot, S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
    GoldfishConeSlotInputsOn S rho Hs s C.erase
  voteActive : ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
    ∀ w ∈ Hs (vote_time S.E d),
      C.erase ∈ get_filtered_block_tree (voteDutyStore S rho w d).toHealing.toFG
  actionActive : ∀ w ∈ Hs (S.a q), C.erase ∈ get_filtered_block_tree (healStoreAt S rho w q).toFG
  voteAnchor : ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
    ∀ w ∈ Hs (vote_time S.E d), voterAnchorAt S rho w d ⪯ C.erase
  confirmationAnchor : ∀ s : Slot, S.hc.opening_slot q - 1 ≤ s → s < seedRoundLastSlot S q →
    ∀ w ∈ Hs (confirmation_time S.E s), confirmationAnchorAt S rho w s ⪯ C.erase
  actionAnchor : ∀ w ∈ Hs (S.a q),
    PhaseGrades.nodeAnchor S (NamedRecoveryRead.actionDutyRead S rho w q) q ⪯ C.erase
  proposerAnchorCeiling :
    S.E.proposer (S.hc.opening_slot q) ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)) →
      PhaseGrades.nodeAnchor S (NamedRecoveryRead.proposalDutyRead S rho (S.hc.opening_slot q)) q ⪯
        C.erase
  proposerActive :
    S.E.proposer (S.hc.opening_slot q) ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)) →
      C.erase ∈ get_filtered_block_tree (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG
  previousCarriers : ∀ v ∈ Hs (S.a (q - 1)), actionSGBlockAt S rho v (q - 1) ⪯ C.erase
  gateOff : GateOffSeedConeWindowAtOn S rho Hs M (S.hc.opening_slot q) (seedRoundLastSlot S q - 1)
  genuineRun : ∀ w ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)), ∀ D : Block V,
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedRecoveryRead.confirmationInputRead S rho w (S.hc.opening_slot q)).cache)
        S.E S.hc (confStore S rho w (S.hc.opening_slot q)) (S.hc.opening_slot q) D →
      ∃ Dn : NamedBlock V, Dn.erase = D ∧ RunBlockOn S rho Xb Dn

/-- At every read of round `q + 1` (vote duties, confirmations from the boundary slot, the opening
    proposer's), the reader's finality root is an ancestor of `C`. -/
structure RoundCeilingNextRootOrderAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot, S.hc.opening_slot (q + 1) ≤ d → d ≤ seedRoundLastSlot S (q + 1) →
    ∀ w ∈ Hs (vote_time S.E d), get_fg_root (voteDutyStore S rho w d).toHealing.toFG ⪯ C
  confirmation : ∀ s : Slot, S.hc.opening_slot (q + 1) - 1 ≤ s → s < seedRoundLastSlot S (q + 1) →
    ∀ w ∈ Hs (confirmation_time S.E s), confRoot (confStore S rho w s) ⪯ C
  proposer : S.E.proposer (S.hc.opening_slot (q + 1)) ∈
      Hs (confirmation_time S.E (S.hc.opening_slot (q + 1))) →
    get_fg_root (proposerDutyStore S rho (S.hc.opening_slot (q + 1))).toHealing.toFG ⪯ C

/-- Round `q + 1` is post-GST, and its boundary confirmers, action readers and proposal-instant
    readers, each taken from `Hs` at the instant of its read, are at frontier `M` with
    `h_j + 2 ≤ M`. -/
structure RoundCeilingNextRegimeAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (M : Height) (q : Round) : Prop where
  postOpeningProposal : S.E.t_GST ≤ proposal_time S.E (S.hc.opening_slot (q + 1))
  roundConfirmationInHorizon : confirmation_time S.E (seedRoundLastSlot S (q + 1) - 1) ≤ rho.horizon
  window : GateOffSeedConeWindowAtOn S rho Hs M (S.hc.opening_slot (q + 1))
    (seedRoundLastSlot S (q + 1) - 1)
  boundaryConfirmationFrontier : ∀ w ∈ Hs (confirmation_time S.E (S.hc.opening_slot (q + 1) - 1)),
    (confStore S rho w (S.hc.opening_slot (q + 1) - 1)).h_max = M
  boundaryConfirmationGateOff : ∀ w ∈ Hs (confirmation_time S.E (S.hc.opening_slot (q + 1) - 1)),
    (confStore S rho w (S.hc.opening_slot (q + 1) - 1)).h_j + 2 ≤ M
  actionFrontier : ∀ w ∈ Hs (S.a (q + 1)), (healStoreAt S rho w (q + 1)).h_max = M
  actionGateOff : ∀ w ∈ Hs (S.a (q + 1)), (healStoreAt S rho w (q + 1)).h_j + 2 ≤ M
  proposalFrontier : ∀ w ∈ Hs (proposal_time S.E (S.hc.opening_slot (q + 1))),
    (Run.storeBeforeTime S rho w (proposal_time S.E (S.hc.opening_slot (q + 1)))).h_max = M
  proposalGateOff : ∀ w ∈ Hs (proposal_time S.E (S.hc.opening_slot (q + 1))),
    (Run.storeBeforeTime S rho w (proposal_time S.E (S.hc.opening_slot (q + 1)))).h_j + 2 ≤ M

/-- The boundary cone of round `q + 1` at `C`: `C` is a run block, the thin honest head and the
    honest votes of the boundary slot descend from `C`, the round-`q` carriers are ancestors of `C`,
    and `RoundCeilingNextRootOrderAtOn` holds. -/
structure RoundCeilingBoundaryConeAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (M : Height) (q : Round) (C : NamedBlock V) : Prop where
  run : RunBlockOn S rho Xb C
  boundaryThinHead : ThinHonestHeadAtOn S rho Hs Xb M (S.hc.opening_slot (q + 1) - 1) C.erase
  postAction : S.E.t_GST ≤ S.a q
  postBoundaryVote : S.E.t_GST ≤ vote_time S.E (S.hc.opening_slot (q + 1) - 1)
  boundaryVotes : NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot (q + 1) - 1)
    fun X => C.erase ⪯ X
  previousCarriers : ∀ v ∈ Hs (S.a q), actionSGBlockAt S rho v q ⪯ C.erase
  rootOrder : RoundCeilingNextRootOrderAtOn S rho Hs q C.erase

/-- The conditions of `RoundCeilingAtOn` at round `q + 1` for `Cstar` that remain after the boundary
    cone, each validator taken from `Hs` at the instant of its read. -/
structure RoundCeilingStepResidualAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (M : Height) (q : Round) (Cstar : Block V) : Prop where
  postOpeningProposal : S.E.t_GST ≤ proposal_time S.E (S.hc.opening_slot (q + 1))
  roundConfirmationInHorizon : confirmation_time S.E (seedRoundLastSlot S (q + 1) - 1) ≤ rho.horizon
  openingStepInputs : ∀ w ∈ Hs (vote_time S.E (S.hc.opening_slot (q + 1) - 1 + 1)),
    GoldfishConeVoteInputs S rho (S.hc.opening_slot (q + 1) - 1) Cstar w
  roundInputs : ∀ s : Slot, S.hc.opening_slot (q + 1) ≤ s → s < seedRoundLastSlot S (q + 1) →
    GoldfishConeSlotInputsOn S rho Hs s Cstar
  voteActive : ∀ d : Slot, S.hc.opening_slot (q + 1) ≤ d → d ≤ seedRoundLastSlot S (q + 1) →
    ∀ w ∈ Hs (vote_time S.E d), Cstar ∈ get_filtered_block_tree (voteDutyStore S rho w d).toHealing.toFG
  actionActive : ∀ w ∈ Hs (S.a (q + 1)),
    Cstar ∈ get_filtered_block_tree (healStoreAt S rho w (q + 1)).toFG
  voteAnchor : ∀ d : Slot, S.hc.opening_slot (q + 1) ≤ d → d ≤ seedRoundLastSlot S (q + 1) →
    ∀ w ∈ Hs (vote_time S.E d), voterAnchorAt S rho w d ⪯ Cstar
  confirmationAnchor : ∀ s : Slot, S.hc.opening_slot (q + 1) - 1 ≤ s →
    s < seedRoundLastSlot S (q + 1) →
      ∀ w ∈ Hs (confirmation_time S.E s), confirmationAnchorAt S rho w s ⪯ Cstar
  actionAnchor : ∀ w ∈ Hs (S.a (q + 1)),
    PhaseGrades.nodeAnchor S (NamedRecoveryRead.actionDutyRead S rho w (q + 1)) (q + 1) ⪯ Cstar
  proposerAnchorCeiling : S.E.proposer (S.hc.opening_slot (q + 1)) ∈
      Hs (confirmation_time S.E (S.hc.opening_slot (q + 1))) →
    PhaseGrades.nodeAnchor S (NamedRecoveryRead.proposalDutyRead S rho (S.hc.opening_slot (q + 1)))
      (q + 1) ⪯ Cstar
  proposerActive : S.E.proposer (S.hc.opening_slot (q + 1)) ∈
      Hs (confirmation_time S.E (S.hc.opening_slot (q + 1))) →
    Cstar ∈ get_filtered_block_tree (proposerDutyStore S rho (S.hc.opening_slot (q + 1))).toHealing.toFG
  gateOff : GateOffSeedConeWindowAtOn S rho Hs M (S.hc.opening_slot (q + 1))
    (seedRoundLastSlot S (q + 1) - 1)
  genuineRun : ∀ w ∈ Hs (confirmation_time S.E (S.hc.opening_slot (q + 1))), ∀ D : Block V,
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedRecoveryRead.confirmationInputRead S rho w (S.hc.opening_slot (q + 1))).cache)
        S.E S.hc (confStore S rho w (S.hc.opening_slot (q + 1))) (S.hc.opening_slot (q + 1)) D →
      ∃ Dn : NamedBlock V, Dn.erase = D ∧ RunBlockOn S rho Xb Dn

/-- The previous ceiling together with the round-`q` action output of every member of `Hs (S.a q)`. -/
def roundCeilingFrontierCandidatesOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (q : Round) (C : NamedBlock V) : Finset (Block V) :=
  insert C.erase (Finset.image (roundCeilingOpeningOutput S rho q) (Hs (S.a q)))

/-- `Cstar` is the deepest of the candidates, a run block read through `Xb`, a descendant of `C` and
    of every output of `Hs (S.a q)`, and is `C` or one of those outputs. -/
structure RoundCeilingFrontierAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (q : Round) (C Cstar : NamedBlock V) : Prop where
  selected : Block.deepest? (roundCeilingFrontierCandidatesOn S rho Hs q C) = some Cstar.erase
  run : RunBlockOn S rho Xb Cstar
  oldPreceq : C.erase ⪯ Cstar.erase
  outputsPreceq : ∀ v ∈ Hs (S.a q), roundCeilingOpeningOutput S rho q v ⪯ Cstar.erase
  source : Cstar = C ∨ ∃ v ∈ Hs (S.a q), roundCeilingOpeningOutput S rho q v = Cstar.erase

/-- The vote-duty and confirmation conditions of round `q + 1` at `C`, each validator taken from
    `Hs` at the instant of its read. -/
structure RoundCeilingRelayFoldAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  openingStepInputs : ∀ w ∈ Hs (vote_time S.E (S.hc.opening_slot (q + 1) - 1 + 1)),
    GoldfishConeVoteInputs S rho (S.hc.opening_slot (q + 1) - 1) C w
  roundInputs : ∀ s : Slot, S.hc.opening_slot (q + 1) ≤ s → s < seedRoundLastSlot S (q + 1) →
    GoldfishConeSlotInputsOn S rho Hs s C
  voteActive : ∀ d : Slot, S.hc.opening_slot (q + 1) ≤ d → d ≤ seedRoundLastSlot S (q + 1) →
    ∀ w ∈ Hs (vote_time S.E d), C ∈ get_filtered_block_tree (voteDutyStore S rho w d).toHealing.toFG
  voteAnchor : ∀ d : Slot, S.hc.opening_slot (q + 1) ≤ d → d ≤ seedRoundLastSlot S (q + 1) →
    ∀ w ∈ Hs (vote_time S.E d), voterAnchorAt S rho w d ⪯ C
  confirmationAnchor : ∀ s : Slot, S.hc.opening_slot (q + 1) - 1 ≤ s →
    s < seedRoundLastSlot S (q + 1) →
      ∀ w ∈ Hs (confirmation_time S.E s), confirmationAnchorAt S rho w s ⪯ C

/-- The finality roots read at the reads of round `q + 1`, each reader taken from `Hs` at the
    instant of its read. -/
def seedRootReadCandidatesOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) :
    Finset (Block V) :=
  (((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
        DecoupledConsensusModel.Proofs.HealingSurface.seedSlotRange)
      (S.hc.opening_slot (q + 1)) (seedRoundLastSlot S (q + 1))).biUnion
      (fun d => (Hs (vote_time S.E d)).image (fun w =>
        get_fg_root (voteDutyStore S rho w d).toHealing.toFG))) ∪
    ((((priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
          DecoupledConsensusModel.Proofs.HealingSurface.seedSlotRange)
        (S.hc.opening_slot (q + 1) - 1) (seedRoundLastSlot S (q + 1) - 1)).biUnion
        (fun s => (Hs (confirmation_time S.E s)).image (fun w =>
          confRoot (confStore S rho w s)))) ∪
      ((Hs (proposal_time S.E (S.hc.opening_slot (q + 1)))).image (fun w =>
        get_fg_root
          (Run.storeBeforeTime S rho w
            (proposal_time S.E (S.hc.opening_slot (q + 1)))).toHealing.toFG)))

/-- `C` is an ancestor of the parent of round `q`'s opening proposal and a descendant of the opening
    slot's votes, sources and previous carriers, each validator taken from `Hs` at the instant of
    its read. -/
structure OpeningCeilingAlignedAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (q : Round) (C : Block V) : Prop where
  sourceBelowCeiling :
    PhaseGrades.nodeAnchor S (NamedRecoveryRead.proposalDutyRead S rho (S.hc.opening_slot q)) q ⪯ C
  voteBelowCeiling : ∀ v ∈ Hs (vote_time S.E (S.hc.opening_slot q)),
    voterAnchorAt S rho v (S.hc.opening_slot q) ⪯ C
  ceilingBelowParent : C ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q)
  confirmationBelowProposal : ∀ v ∈ Hs (confirmation_time S.E (S.hc.opening_slot q)),
    ∀ P : NamedBlock V, Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      confirmationAnchorAt S rho v (S.hc.opening_slot q) ⪯ P.erase
  previousCarriersBelowParent : ∀ v ∈ Hs (S.a (q - 1)),
    actionSGBlockAt S rho v (q - 1) ⪯ Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q)

/-- `C` is the round-`q` action carrier of a member of `Hs (S.a q)` with a run-block witness at
    height at least `M − 1` in its tree, `C` erases a run block, and every member of `Hs (S.a q)`
    has a round-`q` carrier that is an ancestor of `C`. -/
structure DeepestActionCarrierCeilingAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (M : Height) (q : Round) (C : Block V) : Prop where
  sourceAndWitness : ∃ v ∈ Hs (S.a q), actionSGBlockAt S rho v q = C ∧
    ∃ W : NamedBlock V, W.erase ∈ (actionStoreAt S rho v q).st.core.T ∧ C ⪯ W.erase ∧
      RunBlockOn S rho Xb W ∧ M - 1 ≤ (derive_named S.E S.cfg W).h
  run : ∃ D : NamedBlock V, D.erase = C ∧ RunBlockOn S rho Xb D
  previousCarriers : ∀ v ∈ Hs (S.a q), actionSGBlockAt S rho v q ⪯ C

/-! ## The seed -/

/-- Every member of `Hs (S.a (q − 1))` selects a grade-2 candidate at round `q − 1`'s action read,
    and every member of `Hs (S.a q)` at round `q`'s. -/
structure SeedRoundGradedAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (q : Round) :
    Prop where
  selectedPrev : ∀ v ∈ Hs (S.a (q - 1)), ∃ Q : Block V,
    PhaseGrades.nodeQ2 S (actionReadAt S rho v (q - 1)) (q - 1) = some Q
  selected : ∀ v ∈ Hs (S.a q), ∃ Q : Block V, PhaseGrades.nodeQ2 S (actionReadAt S rho v q) q = some Q

/-- Every member of `Hs (S.a q)` selects a grade-2 candidate at round `q`, and every member of
    `Hs (vote_time (seedRoundLastSlot q))` grades 2 at round `q` a run block at height at least
    `M − 1` held at every vote duty of round `q`. -/
def SeedRoundBandGradeAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (M : Height) (q : Round) : Prop :=
  (∀ v ∈ Hs (S.a q), ∃ Q : Block V, PhaseGrades.nodeQ2 S (actionReadAt S rho v q) q = some Q) ∧
    ∀ w ∈ Hs (vote_time S.E (seedRoundLastSlot S q)),
      ∃ Qn : NamedBlock V, RunBlockOn S rho Xb Qn ∧ M - 1 ≤ (derive_named S.E S.cfg Qn).h ∧
        G2 S.E (gradeViewAt S rho w q) S.hc q Qn.erase = true ∧
          ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
            Qn.erase ∈ (voteDutyStore S rho w d).T

/-- Some run block at height at least `M − 1` is an ancestor of the round-`q` carrier of every
    member of `Hs (S.a q)`. -/
def SeedBandCarrierCoverAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (M : Height) (q : Round) : Prop :=
  ∃ Qn : NamedBlock V, RunBlockOn S rho Xb Qn ∧ M - 1 ≤ (derive_named S.E S.cfg Qn).h ∧
    ActionCarriersCoverOn S rho Hs q Qn.erase

/-- The per-round seed conditions at round `c`: on the carriers of `Hs (S.a c)`, and on the anchors
    and heads of the voters taken from `Hs` at each duty's vote instant. -/
structure SeedRoundDischargeAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (M : Height) (c : Round) : Prop where
  claim1 : ∀ v ∈ Hs (S.a c),
    NamedHonestVotesConeOn S rho Hs Xb (S.hc.opening_slot c + 1) fun X => actionSGBlockAt S rho v c ⪯ X
  anchorCompat : ∀ d : Slot, S.hc.opening_slot c + 1 < d → d ≤ S.hc.opening_slot (c + 1) - 1 →
    ∀ w ∈ Hs (vote_time S.E d), ∀ v ∈ Hs (S.a c),
      (voterAnchorAt S rho w d).compatible (actionSGBlockAt S rho v c) = true
  headBand : ∀ d : Slot, S.hc.opening_slot c ≤ d → d ≤ S.hc.opening_slot (c + 1) - 1 →
    ∀ w ∈ Hs (vote_time S.E d), ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w d ∧ RunBlockOn S rho Xb Hn ∧ M - 1 ≤ (derive_named S.E S.cfg Hn).h

/-- At every round `c` at least three rounds after a base round from `r0`, in a window over `Hs`
    with `h_j + 2 ≤ M` that ends in the horizon, `SeedRoundDischargeAtOn` holds. -/
def SeedDischargeFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 : Round) : Prop :=
  ∀ (M : Height) (base c : Round), r0 ≤ base → 1 ≤ c → base + 3 ≤ c →
    S.E.t_GST ≤ S.a (c - 1) → S.a (c + 2) ≤ rho.horizon →
      GateOffFrameAtOn S rho Hs M (base + 1) (c + 2) → SeedRoundDischargeAtOn S rho Hs Xb M c

/-- In every window over `Hs` with `h_j + 2 ≤ M`, every member of the set for a duty's vote instant
    has, at that duty, a head that erases a run block at height at least `M − 1`. -/
def SeedBandReachFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 : Round) : Prop :=
  ∀ (M : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c → S.E.t_GST ≤ S.a (c - 1) →
    S.a (c + 1) ≤ rho.horizon → GateOffFrameAtOn S rho Hs M (c - 1) (c + 1) →
      ∀ d : Slot, S.hc.opening_slot c ≤ d → d ≤ S.hc.opening_slot (c + 1) - 1 →
        ∀ w ∈ Hs (vote_time S.E d), ∃ Hn : NamedBlock V,
          Hn.erase = voterHeadAt S rho w d ∧ RunBlockOn S rho Xb Hn ∧
            M - 1 ≤ (derive_named S.E S.cfg Hn).h

/-- In every window over `Hs` with `h_j + 2 ≤ M`, every member of `Hs (S.a c)` has a raw grade-2
    block at round `c`'s action read. -/
def SeedRawG2FromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r0 : Round) : Prop :=
  ∀ (M : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c → S.E.t_GST ≤ S.a (c - 1) →
    S.a (c + 1) ≤ rho.horizon → GateOffFrameAtOn S rho Hs M (c - 1) (c + 1) →
      ∀ v ∈ Hs (S.a c), PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c

/-- In every window over `Hs` with `h_j + 2 ≤ M`, every voter's anchor is compatible with every
    carrier, or that carrier's action read has no raw grade-2 block. -/
def SeedAnchorCompatFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (r0 : Round) :
    Prop :=
  ∀ (M : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c → S.E.t_GST ≤ S.a (c - 1) →
    S.a (c + 1) ≤ rho.horizon → GateOffFrameAtOn S rho Hs M (c - 1) (c + 1) →
      ∀ d : Slot, S.hc.opening_slot c + 1 ≤ d → d ≤ S.hc.opening_slot (c + 1) - 1 →
        ∀ w ∈ Hs (vote_time S.E d), ∀ v ∈ Hs (S.a c),
          (voterAnchorAt S rho w d).compatible (actionSGBlockAt S rho v c) = true ∨
            ¬PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c

/-- Round `q` is post-GST and in the horizon, every member of `Hs (S.a q)` is at frontier `M` with
    `h_j + 2 ≤ M`, the round is ready to grade, its selected grade-2 blocks are settled, and
    `RoundCeilingNextRegimeAtOn` holds. -/
structure SeedRoundRegimeAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (M : Height)
    (q : Round) : Prop where
  postAction : S.E.t_GST ≤ S.a q
  postOpeningProposal : S.E.t_GST ≤ proposal_time S.E (S.hc.opening_slot q)
  postBoundaryVote : S.E.t_GST ≤ vote_time S.E (S.hc.opening_slot (q + 1) - 1)
  openingConfirmationInHorizon : confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon
  boundaryConfirmationInHorizon :
    confirmation_time S.E (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon
  frontier : ∀ v ∈ Hs (S.a q), (Run.storeBeforeTime S rho v (S.a q)).h_max = M
  gate : ∀ v ∈ Hs (S.a q), (Run.storeBeforeTime S rho v (S.a q)).h_j + 2 ≤ M
  ready : GradeRoundReady S rho q
  settled : SelectedG2SettledAtOn S rho Hs q
  next : RoundCeilingNextRegimeAtOn S rho Hs M q

/-- Every head voted at round `q`'s last slot by a committee member in the set for that slot's vote
    instant is at height at least `M − 1`; and some run block `C`, with a run-block witness at
    height at least `M − 1` as a descendant, is a descendant of the round-`q` carrier of every
    member of `Hs (S.a q)` and an ancestor of every such head. -/
structure SeedBoundaryAdoptionAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (M : Height) (q : Round) : Prop where
  headThin : ∀ X : NamedBlock V,
    NamedHonestHeadOn S rho (fun _ => Hs (vote_time S.E (S.hc.opening_slot (q + 1) - 1))) Xb
      (S.hc.opening_slot (q + 1) - 1) X →
    M - 1 ≤ (derive_named S.E S.cfg X).h
  entry : ∃ C : NamedBlock V, RunBlockOn S rho Xb C ∧
    (∃ W : NamedBlock V, RunBlockOn S rho Xb W ∧ C.erase ⪯ W.erase ∧
      M - 1 ≤ (derive_named S.E S.cfg W).h) ∧
    (∀ v ∈ Hs (S.a q), actionSGBlockAt S rho v q ⪯ C.erase) ∧
    ∀ X : NamedBlock V,
      NamedHonestHeadOn S rho (fun _ => Hs (vote_time S.E (S.hc.opening_slot (q + 1) - 1))) Xb
        (S.hc.opening_slot (q + 1) - 1) X →
      C.erase ⪯ X.erase

/-- Height progress from the seed: the maximum over `Hs` at the endpoint's action instant exceeds
    `M`; or some member `u` of `Hs read`, at a post-GST `read` up to the endpoint, with
    `S.a base ≤ read` or `u` in the set for `S.a base`, holds a fixed-height justification root at
    `M`; or two opening proposals of carrier rounds `entry < q` exist, the first graded, at height
    `M`, and an ancestor of the second's parent at the same height. -/
def HeightProgressSeedOutcomeOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (Xb : Finset V) (M : Height) (base endpointRound : Round) (delayExtra : Nat := 0) : Prop :=
  M < honestHMaxAtOn S rho Hs (S.a endpointRound) ∨
    (∃ (u : V) (read : Time), u ∈ Hs read ∧ S.E.t_GST ≤ read ∧ read ≤ S.a endpointRound ∧
      (S.a base ≤ read ∨ u ∈ Hs (S.a base)) ∧
      FixedHeightJustificationRootAtReadOn S rho Hs Xb M u read) ∨
      ∃ (entry : Round) (q : Round) (Q : NamedBlock V) (Next : NamedBlock V) (Parent : NamedBlock V),
        base + 1 ≤ entry ∧ entry + 2 + delayExtra ≤ q ∧ q ≤ endpointRound ∧
          ProposerCarrierAtOn S Hs q ∧
            Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot entry) = some Q ∧
              NamedGradeFormsAtOn S rho Hs (q - 1) Q.erase ∧ RunBlockOn S rho Xb Q ∧
                (derive_named S.E S.cfg Q).h = M ∧
                  Statements.Instantiation.proposedBlockAt S rho (S.hc.opening_slot q) = some Next ∧
                    Next.parent? = some Parent ∧ Q.Preceq Parent ∧
                      (derive_named S.E S.cfg Parent).h = (derive_named S.E S.cfg Q).h

/-- From every post-GST base round after `r0` at which every member of `Hs (S.a base)` is at the
    maximum with `h_j + 2 ≤ M`, and whose seed window ends in the horizon,
    `HeightProgressSeedOutcomeOn` holds. -/
def HeightProgressSeedFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 gap : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ base : Round, r0 ≤ base → S.E.t_GST ≤ S.a base →
    (∀ w ∈ Hs (S.a base),
      (Run.storeBeforeTime S rho w (S.a base)).h_max = honestHMaxAtOn S rho Hs (S.a base)) →
    (∀ w ∈ Hs (S.a base),
      (Run.storeBeforeTime S rho w (S.a base)).h_j + 2 ≤ honestHMaxAtOn S rho Hs (S.a base)) →
    S.a (base + seedLag gap delayExtra) ≤ rho.horizon →
      HeightProgressSeedOutcomeOn S rho Hs Xb (honestHMaxAtOn S rho Hs (S.a base)) base
        (base + seedLag gap delayExtra) delayExtra

/-- Every FG source a member of `Hs (S.a (q' − 1))` reads at round `q' − 1`'s action is no higher
    than the parent of `B'`. -/
structure SeedPredPromotionInputsAtOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V)
    (M : Height) (q q' : Round) (B B' : NamedBlock V) : Prop where
  sourceHeightLeNextOpeningParent : ∀ v ∈ Hs (S.a (q' - 1)), ∀ Q : Block V,
    PhaseGrades.nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤ (derive_named S.E S.cfg B'.parent).h

/-- From the base round `r0`, for every graded carrier round `q` with a ceiling, an opening window
    and an opening proposal one height short of the frontier, and every carrier round `q'` at least
    `q + 2 + delayExtra` and at least `r0 + 2` whose round `q' − 2` acts after `t_GST`, with
    `h_j + 2 ≤ M` across `[S.a (q' − 2), S.a q']` over `Hs` and the grade forms of round `q' − 1`
    retained, `SeedPredPromotionInputsAtOn` holds at `(q, q')`. -/
def SeedPredPromotionInputsOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ (M : Height) (q q' : Round) (C C' B B' : NamedBlock V), 2 ≤ M →
    SeedRoundGradedAtOn S rho Hs q → ProposerCarrierAtOn S Hs q →
      RoundCeilingAtOn S rho Hs Xb M q C → NamedGateOffOpeningWindowAtOn S rho Hs M q B →
        (derive_named S.E S.cfg B).h = M - 1 → q + 2 + delayExtra ≤ q' → r0 + 2 ≤ q' →
          ProposerCarrierAtOn S Hs q' → RoundCeilingAtOn S rho Hs Xb M q' C' →
            NamedGateOffOpeningWindowAtOn S rho Hs M q' B' → S.E.t_GST ≤ S.a (q' - 2) →
              S.a q' ≤ rho.horizon →
                (∀ read : Time, S.a (q' - 2) ≤ read → read ≤ S.a q' → ∀ w ∈ Hs read,
                  (Run.storeBeforeTime S rho w read).h_j + 2 ≤ M ∧
                    (Run.storeBeforeTime S rho w read).h_max = M) →
                  RunBlockOn S rho Xb B → NamedGradeFormsAtOn S rho Hs (q' - 1) B.erase →
                    (∀ w ∈ Hs (S.a (q' - 1)), FinalityFilterRetainedAtRead S rho w (S.a (q' - 1)) B.erase) →
                      SeedPredPromotionInputsAtOn S rho Hs M q q' B B'

/-- For every post-GST base round from `r0` with `M := honestHMaxAtOn S rho Hs (S.a base)` at least
    2 and not exceeded at the endpoint, if every member of `Hs` read in the window keeps
    `h_j + 2 ≤ M` and `h_max = M`, then a graded carrier round `q` with a ceiling, an opening window
    and an opening proposal at height `M − 1` yields `HeightProgressSeedOutcomeOn` at `M`. -/
def SeedPredCloserFromOn (S : Setup V) (rho : Run V) (Hs : Int → Finset V) (Xb : Finset V)
    (r0 gap : Round) (delayExtra : Nat := 0) : Prop :=
  ∀ (base q : Round) (Cq P : NamedBlock V), r0 ≤ base → base + 4 ≤ q →
    q + 2 * gap + 6 + 2 * delayExtra ≤ base + seedLag gap delayExtra →
      S.E.t_GST ≤ S.a base → S.a (base + seedLag gap delayExtra) ≤ rho.horizon →
        honestHMaxAtOn S rho Hs (S.a (base + seedLag gap delayExtra)) ≤
            honestHMaxAtOn S rho Hs (S.a base) →
          2 ≤ honestHMaxAtOn S rho Hs (S.a base) →
            (∀ read : Time, S.a (base + 1) ≤ read → read ≤ S.a (base + seedLag gap delayExtra) →
              ∀ w ∈ Hs read,
                (read + S.E.Δ < S.a (base + seedLag gap delayExtra) ∨
                    w ∈ Hs (S.a (base + seedLag gap delayExtra))) →
                (Run.storeBeforeTime S rho w read).h_j + 2 ≤ honestHMaxAtOn S rho Hs (S.a base) ∧
                  (Run.storeBeforeTime S rho w read).h_max = honestHMaxAtOn S rho Hs (S.a base)) →
              SeedRoundGradedAtOn S rho Hs q → ProposerCarrierAtOn S Hs q →
                RoundCeilingAtOn S rho Hs Xb (honestHMaxAtOn S rho Hs (S.a base)) q Cq →
                  NamedGateOffOpeningWindowAtOn S rho Hs (honestHMaxAtOn S rho Hs (S.a base)) q P →
                    (derive_named S.E S.cfg P).h = honestHMaxAtOn S rho Hs (S.a base) - 1 →
                      HeightProgressSeedOutcomeOn S rho Hs Xb (honestHMaxAtOn S rho Hs (S.a base))
                        base (base + seedLag gap delayExtra) delayExtra

end DecoupledConsensusModel.Sts
