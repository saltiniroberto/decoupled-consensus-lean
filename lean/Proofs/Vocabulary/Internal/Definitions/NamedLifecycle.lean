module
public import Proofs.Vocabulary.Internal.Definitions.PhaseGradeQueries
public import Proofs.Vocabulary.Internal.Definitions.NamedProposalPivot
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedConfirmationWalk

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Opening-lifecycle structures for a named proposal

The G1 grade at a reader, the cone of honest Goldfish votes, the voter's candidate tree and anchor,
and the opening-confirmation and frozen-vote structures for a named proposal `P`.
-/


namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `B` has G1 grade at `w`'s G1 read of round `r`. -/
def namedG1At (S : Setup V) (rho : Run V) (w : V) (r : Round) (B : Block V) : Prop :=
  storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 B = true

/-- Every honest member of the slot-`s` committee emits, at the slot-`s` vote time, a Goldfish vote
    for a named run block whose erasure satisfies `tgt`. -/
def NamedHonestVotesCone (S : Setup V) (rho : Run V) (s : Slot) (tgt : Block V → Prop) : Prop :=
  ∀ x ∈ rho.honest, x ∈ S.E.committee s → ∃ X : NamedBlock V, tgt X.erase ∧
    NamedRun.blockInRun S rho X ∧
    NamedRun.emits S rho x (.gfVote ⟨x, s, X.erase.root⟩) (Protocol.vote_time S.E s)

/-- The voter's frozen candidate tree at its vote duty read of slot `k`. -/
def voterCandidateTreeAt (S : Setup V) (rho : Run V) (v : V) (k : Slot) : Finset (Block V) :=
  let st := (voteDutyRead S rho v k).st.core
  Protocol.voter_filtered_block_tree S.E st st.s

/-- The voter's anchor at its vote-duty read of slot `k`, taken at the round of that read's slot. -/
def voterAnchorAt (S : Setup V) (rho : Run V) (v : V) (k : Slot) : Block V :=
  let n := voteDutyRead S rho v k
  nodeAnchor S n (S.hc.round_of n.st.core.s)

/-- Three facts on `v`'s confirmation input read of slot `s` for the proposal `P`: its FG root and
    its SG root are ancestors of `P`, and `P` is in its filtered tree. -/
structure NamedSGOpeningConfirmationRead (S : Setup V) (rho : Run V) (s : Slot) (v : V)
    (P : NamedBlock V) : Prop where
  root : Block.Preceq
    (Protocol.get_fg_root (confirmationInputRead S rho v s).st.core.toHealing.toFG) P.erase
  anchor : Block.Preceq
    (Protocol.get_sg_root_with (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confirmationInputRead S rho v s).st.core.toHealing
      (S.hc.round_of (confirmationInputRead S rho v s).st.core.s)) P.erase
  candidate : P.erase ∈ filteredTree (confirmationInputRead S rho v s)

/-- Facts on `v`'s frozen vote at slot `s + 1` for the proposal `P` and a block `A`: both are in, or
    compatible with, the voter's candidate tree and anchor, and the pivot walk transfers. -/
structure NamedSGOpeningFrozenVoteAt (S : Setup V) (rho : Run V) (s : Slot) (A : Block V)
    (v : V) (P : NamedBlock V) : Prop where
  proposalCandidate : P.erase ∈ voterCandidateTreeAt S rho v (s + 1)
  pivotCandidate : A ∈ (voterCandidateTreeAt S rho v (s + 1)).erase P.erase
  pivotAnchorCompatible : Block.compatible (voterAnchorAt S rho v (s + 1)) A = true
  proposalAnchorCompatible : Block.compatible (voterAnchorAt S rho v (s + 1)) P.erase = true
  pivotPath : Block.Preceq (voterAnchorAt S rho v (s + 1)) A →
    ∀ C : Block V, Block.Preceq (voterAnchorAt S rho v (s + 1)) C →
      C ≠ voterAnchorAt S rho v (s + 1) → Block.Preceq C A →
      C ∈ (voterCandidateTreeAt S rho v (s + 1)).erase P.erase
  suffix : NamedProposalPivotSuffixTransfer S rho (s + 1) A v P
  rawExtra : ∀ u,
    u ∈ Protocol.voter_view S.E (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) →
    u ∉ P.erase.gf_votes.toFinset →
    Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true


end DecoupledConsensusModel.Proofs.HealingSurface

end
