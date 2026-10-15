import Proofs.Instance.Objects
import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Pairs
import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks
import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights

/-!
# The model's constants at the images of the spec's objects

For each constant of `DecoupledConsensusModel` on objects (a reader of a block, a vote or an
attestation, a constructor, a reader of the parameters), what it gives at the image of a spec value
under `toProof` or `toProofNamed`, or what the spec's reader gives at the `toSpec` image of the
model's parameters.
-/

set_option autoImplicit false

namespace Spec

variable {V : Type}

/-! ## Height pairs and finality pairs -/

namespace HeightPair

/-- The image of the empty height pair is the empty height pair. -/
@[simp] theorem toProof_empty :
    HeightPair.empty.toProof = DecoupledConsensusModel.HeightPair.empty := rfl

/-- The image of the timeout vote at the height `h`, whatever its root `b`, is the timeout vote at
    `h`. -/
@[simp] theorem toProof_vote_timeout (h : Height) (b : BlockId) :
    (HeightPair.vote h b true).toProof = DecoupledConsensusModel.HeightPair.timeout h := rfl

/-- The image of the target vote at the height `h` for the root `b` is the target vote at `h` for
    the image of `b`. -/
@[simp] theorem toProof_vote_target (h : Height) (b : BlockId) :
    (HeightPair.vote h b false).toProof =
      DecoupledConsensusModel.HeightPair.target h b.toProof := rfl

/-- The height of the image of a height pair is `HeightPair.pairHeight?` of the height pair: `h` for
    a vote at `h`, `none` for the empty pair. -/
@[simp] theorem toProof_height? (p : HeightPair) : p.toProof.height? = p.pairHeight? := by
  cases p with
  | empty => rfl
  | vote h b timeout => cases timeout <;> rfl

/-- The named image of the empty height pair is the empty `NamedHeightPair`. -/
@[simp] theorem toProofNamed_empty :
    HeightPair.empty.toProofNamed = DecoupledConsensusModel.NamedHeightPair.empty := rfl

/-- The named image of the vote at the height `h` for the root `b`, with the timeout flag `timeout`,
    is the vote at `h` for the image of `b`, with the same flag. -/
@[simp] theorem toProofNamed_vote (h : Height) (b : BlockId) (timeout : Bool) :
    (HeightPair.vote h b timeout).toProofNamed =
      DecoupledConsensusModel.NamedHeightPair.vote h b.toProof timeout := rfl

end HeightPair

namespace FinalityPair

/-- The height of the image of a finality pair is the finality pair's height. -/
@[simp] theorem toProof_height (p : FinalityPair) : p.toProof.height = p.height := rfl

/-- The root of the image of a finality pair is the image of the finality pair's root. -/
@[simp] theorem toProof_target (p : FinalityPair) : p.toProof.target = p.target.toProof := rfl

/-- The image of the finality pair with the height `h` and the root `b` is the finality pair with
    the height `h` and the image of `b`. -/
@[simp] theorem toProof_mk (h : Height) (b : BlockId) :
    (FinalityPair.mk h b).toProof = DecoupledConsensusModel.FinalityPair.mk h b.toProof := rfl

end FinalityPair

/-! ## Goldfish votes and attestations -/

namespace GoldfishVote

/-- The validator of the image of a Goldfish vote is the vote's validator. -/
@[simp] theorem toProof_val_index (vote : GoldfishVote V) :
    vote.toProof.val_index = vote.val_index := rfl

/-- The slot of the image of a Goldfish vote is the vote's slot. -/
@[simp] theorem toProof_slot (vote : GoldfishVote V) : vote.toProof.slot = vote.slot := rfl

/-- The head root of the image of a Goldfish vote is the image of the vote's head root. -/
@[simp] theorem toProof_head (vote : GoldfishVote V) : vote.toProof.head = vote.head.toProof :=
  rfl

/-- The image of the Goldfish vote of the validator `v` at the slot `s` for the root `b` is the
    Goldfish vote of `v` at `s` for the image of `b`. -/
@[simp] theorem toProof_mk (v : V) (s : Slot) (b : BlockId) :
    (GoldfishVote.mk v s b).toProof = DecoupledConsensusModel.GoldfishVote.mk v s b.toProof := rfl

end GoldfishVote

namespace Attestation

/-- The validator of the image of an attestation is the attestation's validator. -/
@[simp] theorem toProof_val_index (a : Attestation V) :
    a.toProof.val_index = a.val_index := rfl

/-- The round of the image of an attestation is the attestation's round. -/
@[simp] theorem toProof_round (a : Attestation V) : a.toProof.round = a.round := rfl

/-- The confirmed root of the image of an attestation is the attestation's confirmed root, mapped
by `BlockId.toProof`; `none` when the attestation confirms no block. -/
@[simp] theorem toProof_confirmed (a : Attestation V) :
    a.toProof.confirmed = a.confirmed.map BlockId.toProof := rfl

/-- The height pair of the image of an attestation is the image of the attestation's height pair. -/
@[simp] theorem toProof_height_pair (a : Attestation V) :
    a.toProof.height_pair = a.height_pair.toProof := rfl

/-- The finality pair of the image of an attestation is the attestation's finality pair, mapped
by `FinalityPair.toProof`; `none` when the attestation has none. -/
@[simp] theorem toProof_finality_pair (a : Attestation V) :
    a.toProof.finality_pair = a.finality_pair.map FinalityPair.toProof := rfl

/-- The image of the attestation built from a validator, a round, a confirmed root, a height pair
    and a finality pair is the `CombinedAttestation` built from the same validator and round and the
    images of the other three. -/
@[simp] theorem toProof_mk (v : V) (r : Round) (c : Option BlockId) (hp : HeightPair)
    (fp : Option FinalityPair) :
    (Attestation.mk v r c hp fp).toProof =
      DecoupledConsensusModel.CombinedAttestation.mk v r (c.map BlockId.toProof) hp.toProof
        (fp.map FinalityPair.toProof) := rfl

/-- The validator of the named image of an attestation is its validator. -/
@[simp] theorem toProofNamed_val_index (a : Attestation V) :
    a.toProofNamed.val_index = a.val_index := rfl

/-- The round of the named image of an attestation is its round. -/
@[simp] theorem toProofNamed_round (a : Attestation V) : a.toProofNamed.round = a.round := rfl

/-- The confirmed root of the named image of an attestation is its confirmed root, mapped by
`BlockId.toProof`. -/
@[simp] theorem toProofNamed_confirmed (a : Attestation V) :
    a.toProofNamed.confirmed = a.confirmed.map BlockId.toProof := rfl

/-- The height pair of the named image of an attestation is the named image of its height pair. -/
@[simp] theorem toProofNamed_height_pair (a : Attestation V) :
    a.toProofNamed.height_pair = a.height_pair.toProofNamed := rfl

/-- The finality pair of the named image of an attestation is its finality pair, mapped by
`FinalityPair.toProof`. -/
@[simp] theorem toProofNamed_finality_pair (a : Attestation V) :
    a.toProofNamed.finality_pair = a.finality_pair.map FinalityPair.toProof := rfl

/-- The named image of the attestation built from a validator, a round, a confirmed root, a height
    pair and a finality pair is the `NamedAttestation` built from the same validator and round, the
    images of the confirmed root and of the finality pair, and the named image of the height pair. -/
@[simp] theorem toProofNamed_mk (v : V) (r : Round) (c : Option BlockId) (hp : HeightPair)
    (fp : Option FinalityPair) :
    (Attestation.mk v r c hp fp).toProofNamed =
      DecoupledConsensusModel.NamedAttestation.mk v r (c.map BlockId.toProof) hp.toProofNamed
        (fp.map FinalityPair.toProof) := rfl

end Attestation

/-! ## Blocks -/

namespace Block

/-- The slot of the image of a block is the block's slot. -/
@[simp] theorem toProof_slot (B : Block V) : B.toProof.slot = B.slot := by
  cases B <;> rfl

/-- The parent of the image of a block is the image of the block's parent. -/
@[simp] theorem toProof_parent (B : Block V) : B.toProof.parent = B.parent.toProof := by
  cases B <;> rfl

/-- The optional parent of the image of a block is the block's optional parent, mapped by
    `Block.toProof`. -/
@[simp] theorem toProof_parent? (B : Block V) : B.toProof.parent? = B.parent?.map Block.toProof := by
  cases B <;> rfl

/-- The Goldfish votes the image of a block includes are the images of those the block includes. -/
@[simp] theorem toProof_gf_votes (B : Block V) :
    B.toProof.gf_votes = B.gf_votes.map GoldfishVote.toProof := by
  cases B <;> rfl

/-- The resolved Goldfish votes of the image of a block are the images of the block's. -/
@[simp] theorem toProof_gf_support_votes (B : Block V) :
    B.toProof.gf_support_votes = B.gf_support_votes.map GoldfishVote.toProof := by
  cases B <;> rfl

/-- The attestations the image of a block includes are the images of those the block includes. -/
@[simp] theorem toProof_attestations (B : Block V) :
    B.toProof.attestations = B.attestations.map Attestation.toProof := by
  cases B <;> rfl

/-- The proposer of the image of a block is the block's proposer. -/
@[simp] theorem toProof_proposer? (B : Block V) : B.toProof.proposer? = B.proposer? := by
  cases B <;> rfl

/-- The image of a block built by `Block.node` is the block built from the image of the parent, the
    same slot, the image of the root, the images of the votes and of the attestations, and the same
    proposer. -/
@[simp] theorem toProof_node (p : Block V) (s : Slot) (r : BlockId) (votes : List (GoldfishVote V))
    (support : List (GoldfishVote V)) (ats : List (Attestation V)) (proposer : V) :
    (Block.node p s r votes support ats proposer).toProof =
      DecoupledConsensusModel.Block.node p.toProof s r.toProof (votes.map GoldfishVote.toProof)
        (support.map GoldfishVote.toProof) (ats.map Attestation.toProof) proposer := rfl

/-- The named image of a block built by `Block.node` is the `NamedBlock` built from the named image
    of the parent, the same slot, the image of the root, the images of the votes, the named images
    of the attestations, and the same proposer. -/
@[simp] theorem toProofNamed_node (p : Block V) (s : Slot) (r : BlockId)
    (votes : List (GoldfishVote V)) (support : List (GoldfishVote V))
    (ats : List (Attestation V)) (proposer : V) :
    (Block.node p s r votes support ats proposer).toProofNamed =
      DecoupledConsensusModel.NamedBlock.node p.toProofNamed s r.toProof
        (votes.map GoldfishVote.toProof) (support.map GoldfishVote.toProof)
        (ats.map Attestation.toProofNamed) proposer := rfl

/-- The slot of the named image of a block is its slot. -/
@[simp] theorem toProofNamed_slot (B : Block V) : B.toProofNamed.slot = B.slot := by
  cases B <;> rfl

/-- The root of the named image of a block is the image of its root. -/
@[simp] theorem toProofNamed_root (B : Block V) : B.toProofNamed.root = B.root.toProof := by
  cases B <;> rfl

/-- The parent of the named image of a block is the named image of its parent. -/
@[simp] theorem toProofNamed_parent (B : Block V) :
    B.toProofNamed.parent = B.parent.toProofNamed := by
  cases B <;> rfl

/-- The optional parent of the named image of a block is the block's optional parent, mapped by
    `Block.toProofNamed`. -/
@[simp] theorem toProofNamed_parent? (B : Block V) :
    B.toProofNamed.parent? = B.parent?.map Block.toProofNamed := by
  cases B <;> rfl

/-- The Goldfish votes the named image of a block includes are the images of those it includes. -/
@[simp] theorem toProofNamed_gf_votes (B : Block V) :
    B.toProofNamed.gf_votes = B.gf_votes.map GoldfishVote.toProof := by
  cases B <;> rfl

/-- The resolved Goldfish votes of the named image of a block are the images of the block's. -/
@[simp] theorem toProofNamed_gf_support_votes (B : Block V) :
    B.toProofNamed.gf_support_votes = B.gf_support_votes.map GoldfishVote.toProof := by
  cases B <;> rfl

/-- The attestations the named image of a block includes are the named images of those it includes. -/
@[simp] theorem toProofNamed_attestations (B : Block V) :
    B.toProofNamed.attestations = B.attestations.map Attestation.toProofNamed := by
  cases B <;> rfl

/-- The proposer of the named image of a block is the block's proposer. -/
@[simp] theorem toProofNamed_proposer? (B : Block V) : B.toProofNamed.proposer? = B.proposer? := by
  cases B <;> rfl

end Block

/-! ## Weights -/

namespace Electorate

variable [Fintype V]

/-- The weight of a validator in the image of the weights is its weight. -/
@[simp] theorem toProof_weight (E : Electorate V) : E.toProof.weight = E.weight := rfl

/-- The weight of a set of validators, read from the image of the weights of `P`, is `P.weightOf`. -/
@[simp] theorem toProof_weightOf (P : Provisional V) (S : Finset V) :
    P.electorate.toProof.weightOf S = P.weightOf S := rfl

/-- The total weight, read from the image of the weights of `P`, is `P.totalWeight`. -/
@[simp] theorem toProof_totalWeight (P : Provisional V) :
    P.electorate.toProof.totalWeight = P.totalWeight := rfl

end Electorate

/-! ## The objects a node sends -/

namespace NamedObject

/-- The image of the object holding the block `B` is the object holding the named image of `B`. -/
@[simp] theorem toProof_block (B : Block V) :
    (NamedObject.block B).toProof =
      DecoupledConsensusModel.Execution.NamedObject.block B.toProofNamed :=
  rfl

/-- The image of the object holding the Goldfish vote `vote` is the object holding the image of
    `vote`. -/
@[simp] theorem toProof_gfVote (vote : GoldfishVote V) :
    (NamedObject.gfVote vote).toProof =
      DecoupledConsensusModel.Execution.NamedObject.gfVote vote.toProof := rfl

/-- The image of the object holding the attestation `a` is the object holding the named image of
    `a`. -/
@[simp] theorem toProof_attest (a : Attestation V) :
    (NamedObject.attest a).toProof =
      DecoupledConsensusModel.Execution.NamedObject.attest a.toProofNamed :=
  rfl

end NamedObject

namespace Protocol

/-! ## SG votes, tokens and phases -/

namespace SGVote

/-- The validator of the image of an SG vote is the vote's validator. -/
@[simp] theorem toProof_val_index (u : SGVote V) : u.toProof.val_index = u.val_index := rfl

/-- The round of the image of an SG vote is the vote's round. -/
@[simp] theorem toProof_round (u : SGVote V) : u.toProof.round = u.round := rfl

/-- The confirmed root of the image of an SG vote is the vote's confirmed root, mapped by
    `BlockId.toProof`. -/
@[simp] theorem toProof_confirmed (u : SGVote V) :
    u.toProof.confirmed = u.confirmed.map BlockId.toProof := rfl

/-- The image of the SG vote of the validator `v` at the round `r` for the confirmed root `c` is the
    SG vote of `v` at `r` for the image of `c`. -/
@[simp] theorem toProof_mk (v : V) (r : Round) (c : Option BlockId) :
    (SGVote.mk v r c).toProof =
      DecoupledConsensusModel.Protocol.SGVote.mk v r (c.map BlockId.toProof) := rfl

end SGVote

namespace Token

/-- The round of the image of a token is the token's round. -/
@[simp] theorem toProof_round (x : Token (Option BlockId)) : x.toProof.round = x.round := rfl

/-- The key of the image of a token is the token's key, mapped by `BlockId.toProof`. -/
@[simp] theorem toProof_key (x : Token (Option BlockId)) :
    x.toProof.key = x.key.map BlockId.toProof := rfl

/-- The image of the token with the round `r` and the key `k` is the token with the round `r` and
    the key `k` mapped by `BlockId.toProof`. -/
@[simp] theorem toProof_mk (r : Nat) (k : Option BlockId) :
    (Token.mk r k).toProof = DecoupledConsensusModel.Protocol.Token.mk r (k.map BlockId.toProof) :=
  rfl

end Token

namespace Phase

/-- The image of the grade-0 phase is the grade-0 phase. -/
@[simp] theorem toProof_g0 : Phase.g0.toProof = DecoupledConsensusModel.Protocol.Phase.g0 := rfl

/-- The image of the grade-1 phase is the grade-1 phase. -/
@[simp] theorem toProof_g1 : Phase.g1.toProof = DecoupledConsensusModel.Protocol.Phase.g1 := rfl

/-- The image of the grade-2 phase is the grade-2 phase. -/
@[simp] theorem toProof_g2 : Phase.g2.toProof = DecoupledConsensusModel.Protocol.Phase.g2 := rfl

end Phase

/-! ## The inputs of the duties -/

namespace ProposalInput

/-- The parent of the image of a proposal input is the image of its parent. -/
@[simp] theorem toProof_parent (x : ProposalInput V) : x.toProof.parent = x.parent.toProof := rfl

/-- The slot of the image of a proposal input is its slot. -/
@[simp] theorem toProof_slot (x : ProposalInput V) : x.toProof.slot = x.slot := rfl

/-- The root of the image of a proposal input is the image of its root. -/
@[simp] theorem toProof_root (x : ProposalInput V) : x.toProof.root = x.root.toProof := rfl

/-- The Goldfish votes of the image of a proposal input are the images of its Goldfish votes. -/
@[simp] theorem toProof_gf_votes (x : ProposalInput V) :
    x.toProof.gf_votes = x.gf_votes.map GoldfishVote.toProof := rfl

/-- The resolved Goldfish votes of the image of a proposal input are the images of its resolved
    Goldfish votes. -/
@[simp] theorem toProof_gf_support_votes (x : ProposalInput V) :
    x.toProof.gf_support_votes = x.gf_support_votes.map GoldfishVote.toProof := rfl

/-- The proposer of the image of a proposal input is its proposer. -/
@[simp] theorem toProof_proposer (x : ProposalInput V) : x.toProof.proposer = x.proposer := rfl

end ProposalInput

namespace AttestationInput

/-- The confirmed root of the image of an attestation input is its confirmed root, mapped by
    `BlockId.toProof`. -/
@[simp] theorem toProof_confirmed (x : AttestationInput V) :
    x.toProof.confirmed = x.confirmed.map BlockId.toProof := rfl

/-- The triple `fields` of the image of an attestation input is its triple with the root mapped by
    `BlockId.toProof`. -/
@[simp] theorem toProof_fields (x : AttestationInput V) :
    x.toProof.fields = x.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2)) := rfl

end AttestationInput

/-! ## Grade reads -/

namespace GradeRead

/-- The anchor of the image of a grade read is the image of its anchor. -/
@[simp] theorem toProof_anchor (g : GradeRead V) : g.toProof.anchor = g.anchor.toProof := rfl

/-- The grade-2 candidate of the image of a grade read is its grade-2 candidate, mapped by
    `Block.toProof`. -/
@[simp] theorem toProof_Q2 (g : GradeRead V) : g.toProof.Q2 = g.Q2.map Block.toProof := rfl

/-- The grade-0 test of the image of a grade read, at a block `B` of `DecoupledConsensusModel`, is
    the grade read's test at `Block.toSpec B`. -/
@[simp] theorem toProof_clear_apply (g : GradeRead V) (B : DecoupledConsensusModel.Block V) :
    g.toProof.clear B = g.clear (Block.toSpec B) := rfl

/-- The proposition `rawG2` of the image of a grade read holds exactly when the grade read's Boolean
    `rawG2` is `true`. -/
@[simp] theorem toProof_rawG2 (g : GradeRead V) : g.toProof.rawG2 ↔ g.rawG2 = true := Iff.rfl

end GradeRead

end Protocol

/-! ## The parameters -/

section Parameters

variable [DecidableEq V] [Fintype V]

namespace Config

variable (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
  (cfg : DecoupledConsensusModel.Protocol.HeightConfig)

/-- The schedule unit `Δ` of `Config.toSpec E hc cfg` is the environment's `E.Δ`. -/
@[simp] theorem toSpec_Δ : (Config.toSpec E hc cfg).Δ = E.Δ := rfl

/-- The round length `R` of `Config.toSpec E hc cfg` is the round schedule's `hc.R`. -/
@[simp] theorem toSpec_R : (Config.toSpec E hc cfg).R = hc.R := rfl

/-- The lookback `η_SG` of `Config.toSpec E hc cfg` is the round schedule's `hc.η_SG`. -/
@[simp] theorem toSpec_η_SG : (Config.toSpec E hc cfg).η_SG = hc.η_SG := rfl

/-- The period `K` of `Config.toSpec E hc cfg` is the height parameters' `cfg.K`. -/
@[simp] theorem toSpec_K : (Config.toSpec E hc cfg).K = cfg.K := rfl

/-- The bound `D` of `Config.toSpec E hc cfg` is the height parameters' `cfg.D`. -/
@[simp] theorem toSpec_D : (Config.toSpec E hc cfg).D = cfg.D := rfl

/-- The delay `timeoutDelay` of `Config.toSpec E hc cfg` is `cfg.timeoutDelay`. -/
@[simp] theorem toSpec_timeoutDelay :
    (Config.toSpec E hc cfg).timeoutDelay = cfg.timeoutDelay := rfl

/-- The slot containing the time `t`, read from `Config.toSpec E hc cfg`, is `E.slotOf t`. -/
@[simp] theorem toSpec_slotOf (t : Time) : (Config.toSpec E hc cfg).slotOf t = E.slotOf t := rfl

/-- The proposal time of slot `s`, read from `Config.toSpec E hc cfg`, is `slotStart E.Δ s`. -/
@[simp] theorem toSpec_proposal_time (s : Slot) :
    (Config.toSpec E hc cfg).proposal_time s = DecoupledConsensusModel.slotStart E.Δ s := rfl

end Config

namespace Provisional

variable (E : DecoupledConsensusModel.Env V)

/-- The proposer of the slot `s` in `Provisional.toSpec E` is the environment's `E.proposer s`. -/
@[simp] theorem toSpec_proposer (s : Slot) : (Provisional.toSpec E).proposer s = E.proposer s :=
  rfl

/-- The committees of `Provisional.toSpec E` are `Committees.toSpec E.committees`. -/
@[simp] theorem toSpec_committees :
    (Provisional.toSpec E).committees = Committees.toSpec E.committees := rfl

/-- The weights of `Provisional.toSpec E` are `Electorate.toSpec E.electorate`. -/
@[simp] theorem toSpec_electorate :
    (Provisional.toSpec E).electorate = Electorate.toSpec E.electorate := rfl

/-- The committee of the slot `s`, read from `Provisional.toSpec E`, is `E.committee s`. -/
@[simp] theorem toSpec_committee (s : Slot) : (Provisional.toSpec E).committee s = E.committee s :=
  rfl

/-- The weight of the set `S`, read from `Provisional.toSpec E`, is `E.electorate.weightOf S`. -/
@[simp] theorem toSpec_weightOf (S : Finset V) :
    (Provisional.toSpec E).weightOf S = E.electorate.weightOf S := rfl

/-- The total weight, read from `Provisional.toSpec E`, is `E.electorate.totalWeight`. -/
@[simp] theorem toSpec_totalWeight :
    (Provisional.toSpec E).totalWeight = E.electorate.totalWeight := rfl

/-- The quorum threshold, read from `Provisional.toSpec E`, is `E.electorate.finalityThreshold`. -/
@[simp] theorem toSpec_finalityThreshold :
    (Provisional.toSpec E).finalityThreshold = E.electorate.finalityThreshold := rfl

/-- The quorum test of the set `S`, read from `Provisional.toSpec E`, is
    `E.electorate.quorumCheck S`. -/
@[simp] theorem toSpec_quorumCheck (S : Finset V) :
    (Provisional.toSpec E).quorumCheck S = E.electorate.quorumCheck S := rfl

end Provisional

end Parameters

/-! ## The time functions -/

/-- `stampedBefore ts Γ x`, whether `x` has a stamp in `ts` strictly before the time `Γ`, is the
    spec's `occurrenceBefore (ts x) Γ`. -/
@[simp] theorem stampedBefore_eq_occurrenceBefore {α : Type} (ts : TimestampMap α) (Γ : Time)
    (x : α) : DecoupledConsensusModel.stampedBefore ts Γ x = occurrenceBefore (ts x) Γ := by
  rw [occurrenceBefore_eq]
  rfl

/-- `slotStart C.Δ s` is `C.proposal_time s`, the time slot `s` starts. -/
@[simp] theorem Config.slotStart_eq_proposal_time (C : Config) (s : Slot) :
    DecoupledConsensusModel.slotStart C.Δ s = C.proposal_time s := rfl

/-- `slotOfTime C.Δ t` is `C.slotOf t`, the slot containing the time `t`. -/
@[simp] theorem Config.slotOfTime_eq_slotOf (C : Config) (t : Time) :
    DecoupledConsensusModel.slotOfTime C.Δ t = C.slotOf t := rfl

end Spec
