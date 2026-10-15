import Proofs.Instance.Members.Base

/-!
# The members of the fork-choice and grades families

The definitions of the namespace `SpecDraftRecord.Member` that fill the fork-choice and grades
members of the record `Model V` with the spec's readers and routines, one definition per member,
named as the member. It also holds the embeddings that map sets of blocks, Goldfish votes and tokens
into the spec's types.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open Spec
open scoped DC

namespace ForkChoiceGrades

variable {V : Type}

/-- `Block.toSpec` is injective. -/
theorem blockToSpec_injective :
    Function.Injective (Block.toSpec : DecoupledConsensusModel.Block V → Block V) :=
  Function.LeftInverse.injective (g := Block.toProof) Block.toProof_toSpec

/-- `Block.toSpec` as an embedding, for `Finset.map`. -/
def blockToSpecEmb : DecoupledConsensusModel.Block V ↪ Block V :=
  ⟨Block.toSpec, blockToSpec_injective⟩

/-- `GoldfishVote.toSpec` is injective. -/
theorem voteToSpec_injective :
    Function.Injective (GoldfishVote.toSpec : DecoupledConsensusModel.GoldfishVote V →
      GoldfishVote V) :=
  Function.LeftInverse.injective (g := GoldfishVote.toProof) GoldfishVote.toProof_toSpec

/-- `GoldfishVote.toSpec` as an embedding, for `Finset.map`. -/
def voteToSpecEmb : DecoupledConsensusModel.GoldfishVote V ↪ GoldfishVote V :=
  ⟨GoldfishVote.toSpec, voteToSpec_injective⟩

/-- The token `x` as the spec's token with the same round and the same key. -/
def tokenToSpec {Key : Type} (x : DecoupledConsensusModel.Protocol.Token Key) :
    Protocol.Token Key :=
  ⟨x.round, x.key⟩

/-- `tokenToSpec` is injective. -/
theorem tokenToSpec_injective {Key : Type} :
    Function.Injective (tokenToSpec : DecoupledConsensusModel.Protocol.Token Key →
      Protocol.Token Key) := by
  rintro ⟨r₁, k₁⟩ ⟨r₂, k₂⟩ h
  simp only [tokenToSpec, Protocol.Token.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- `tokenToSpec` as an embedding, for `Finset.map`. -/
def tokenToSpecEmb {Key : Type} :
    DecoupledConsensusModel.Protocol.Token Key ↪ Protocol.Token Key :=
  ⟨tokenToSpec, tokenToSpec_injective⟩

section OfImage

variable [DecidableEq V]

/-- The saved result `result` as a grade result on the store `st`: `none` is `pending`, and `some G`
    is `computed` of `G` with its block read by `st.blockOfImage`. -/
def gradeResultOfImage (st : Store V) :
    Option (Option (DecoupledConsensusModel.Block V)) → GradeResult V
  | none => .pending
  | some G => .computed (G.map st.blockOfImage)

/-- The grade read `g` as the spec's grade read on the store `st`, its blocks read by
    `st.blockOfImage`. -/
def gradeReadOfImage (st : Store V) (g : DecoupledConsensusModel.Protocol.GradeRead V) :
    Protocol.GradeRead V where
  anchor := st.blockOfImage g.anchor
  Q2 := g.Q2.map st.blockOfImage
  clear := fun B => g.clear B.toProof
  rawG2 := @decide g.rawG2 g.rawG2_decidable

end OfImage

end ForkChoiceGrades

namespace Member

open ForkChoiceGrades

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The fork-choice family -/

/-- Record member `toGoldfishStore`: the identity, since the spec has one store type. -/
def toGoldfishStore : Store V → Store V := id

/-- Record member `sgs_sg_votes`: the SG votes of round `r` in `st`, each mapped by
    `SGVote.toProof`. -/
def sgs_sg_votes (st : Store V) (r : Round) :
    Finset (DecoupledConsensusModel.Protocol.SGVote V) :=
  (st.sg_votes r).map Protocol.SGVote.toProofEmb

/-- Record member `toSG`: the identity, since the spec has one store type. -/
def toSG : Store V → Store V := id

/-- Record member `fg_σ`: the chain state `st` holds for the block of its tree read from `B` by
    `st.blockOfImage`. -/
def fg_σ (st : Store V) (B : DecoupledConsensusModel.Block V) : Protocol.ChainState V :=
  st.σ (st.blockOfImage B)

/-- Record member `fg_F`: the finalized block of `st`. -/
def fg_F (st : Store V) : DecoupledConsensusModel.Block V := st.F.toProof

/-- Record member `fg_J`: the justified block of `st`. -/
def fg_J (st : Store V) : DecoupledConsensusModel.Block V := st.J.toProof

/-- Record member `fg_h_j`: the justified height of `st`. -/
def fg_h_j (st : Store V) : Height := st.h_j

/-- Record member `fg_h_max`: the largest chain-state height `st` has seen. -/
def fg_h_max (st : Store V) : Height := st.h_max

/-- Record member `get_fg_root`: the spec's `Protocol.get_fg_root` of `st` read through its tree
    (`Store.ofImage`), the fgroot of `st`. -/
def get_fg_root (st : Store V) : DecoupledConsensusModel.Block V :=
  (Protocol.get_fg_root (Store.ofImage st)).toProof

/-- Record member `get_filtered_block_tree`: the spec's `Protocol.get_filtered_block_tree` of `st`
    read through its tree (`Store.ofImage`), the blocks of `st` the fork choice keeps. -/
def get_filtered_block_tree (st : Store V) : Finset (DecoupledConsensusModel.Block V) :=
  (Protocol.get_filtered_block_tree (Store.ofImage st)).image Block.toProof

/-- Record member `get_sg_root_with`: the SG root of the grade-1 result of round `r`, read from the
    saved grades `c` on the store `st`; there is no outcome when the read fails. The environment `E`
    and the round schedule `hc` are not read. -/
def get_sg_root_with (c : SavedGrades V) (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (r : Round) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes (Except.map Block.toProof
    (Protocol.anchor
      { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) }
      (Protocol.round_grades
        { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) }
        r).g1))

/-- Record member `voter_processed_block_tree`: the spec's `Protocol.voter_processed_block_tree`,
    the blocks the slot-`s` voter walks over in `st`; there is no outcome when the routine fails. -/
def voter_processed_block_tree (E : DecoupledConsensusModel.Env V) (st : Store V) (s : Slot) :
    DC.NDRE (Finset (DecoupledConsensusModel.Block V)) :=
  successOutcomes (Except.map (fun T => T.image Block.toProof)
    (Protocol.voter_processed_block_tree (Config.toSpec E unreadHealConfig unreadHeightConfig)
      st s))

/-- Record member `voter_view`: the spec's `Protocol.voter_view`, the Goldfish votes the slot-`s`
    voter counts in `st`; there is no outcome when the routine fails. -/
def voter_view (E : DecoupledConsensusModel.Env V) (st : Store V) (s : Slot) :
    DC.NDRE (Finset (DecoupledConsensusModel.GoldfishVote V)) :=
  successOutcomes (Except.map (fun votes => votes.map GoldfishVote.toProofEmb)
    (Protocol.voter_view (Config.toSpec E unreadHealConfig unreadHeightConfig) st s))

/-- Record member `voters_count`: the spec's `Protocol.raw_voters_count`, the number of validators
    with a vote in `votes`. The environment and the slot are not read. -/
def voters_count (_E : DecoupledConsensusModel.Env V)
    (votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (_s : Slot) : ℕ :=
  Protocol.raw_voters_count (votes.map voteToSpecEmb)

/-- Record member `latest_window`: the spec's `Protocol.latest_window`, the rounds from `r − η_SG`
    (or `0`) up to `r − 1`. -/
def latest_window (η_SG r : Round) : List Round := Protocol.latest_window η_SG r

/-- Record member `goldfish_score`: the Goldfish score of `B` in slot `s`, the spec's
    `Protocol.raw_goldfish_score` when it answers, and
    `DecoupledConsensusModel.Protocol.goldfish_score` when it raises (`orVocabulary`). -/
def goldfish_score (E : DecoupledConsensusModel.Env V)
    (T : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) : DC.NDRE ℕ :=
  successOutcomes (orVocabulary
    (Protocol.raw_goldfish_score (T.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (Block.toSpec B))
    (DecoupledConsensusModel.Protocol.goldfish_score E T votes support_votes s B))

/-- Record member `voter_support_view`: the spec's `Protocol.voter_support_view`, the Goldfish votes
    the slot-`s` voter counts as support in `st`; there is no outcome when the routine fails. -/
def voter_support_view (E : DecoupledConsensusModel.Env V) (st : Store V) (s : Slot) :
    DC.NDRE (Finset (DecoupledConsensusModel.GoldfishVote V)) :=
  successOutcomes (Except.map (fun votes => votes.map GoldfishVote.toProofEmb)
    (Protocol.voter_support_view (Config.toSpec E unreadHealConfig unreadHeightConfig) st s))

/-- Record member `proposer_view`: the spec's `Protocol.proposer_view`, the Goldfish votes of slot
    `s − 1` that `st` holds. -/
def proposer_view (st : Store V) (s : Slot) : List (DecoupledConsensusModel.GoldfishVote V) :=
  (Protocol.proposer_view st s).map GoldfishVote.toProof

/-- Record member `get_head_with`: the spec's `Protocol.get_head_with`, the fork-choice head of `st`
    at slot `s` with its saved grades read from `c`; there is no outcome when the routine fails. -/
def get_head_with (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V)
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes (Except.map Block.toProof
    (Protocol.get_head_with (Config.toSpec E hc unreadHeightConfig)
      { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round
          (st.contractOfImage c) ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        (votes.map voteToSpecEmb) (support_votes.map voteToSpecEmb)
      s))

/-- Record member `ghost`: the spec's `Protocol.ghost`, the walk from `B` through `tree` with the
    score `score` and the test `eligible`; an outcome is the block it stops at. -/
def ghost (B : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    (score : DecoupledConsensusModel.Block V → ℕ) (eligible : DecoupledConsensusModel.Block V → Bool) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes (Except.map Block.toProof
    (Protocol.ghost (Block.toSpec B) (tree.map blockToSpecEmb)
      (fun C => pure (score C.toProof)) (fun C => pure (eligible C.toProof))))

/-- Record member `proposer_support_view`: the spec's `Protocol.proposer_support_view`, the Goldfish
    votes the slot-`s` proposer counts as support in `st`; there is no outcome when the routine
    fails. -/
def proposer_support_view (st : Store V) (s : Slot) :
    DC.NDRE (List (DecoupledConsensusModel.GoldfishVote V)) :=
  successOutcomes (Except.map (fun votes => votes.map GoldfishVote.toProof)
    (Protocol.proposer_support_view st s))

/-- Record member `goldfish_eligible`: whether the Goldfish walk may step onto `B`, the spec's
    `Protocol.goldfish_eligible` when it answers, and
    `DecoupledConsensusModel.Protocol.goldfish_eligible` when it raises (`orVocabulary`). -/
def goldfish_eligible (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) : DC.NDRE Bool :=
  successOutcomes (orVocabulary
    (Protocol.goldfish_eligible (fun C => σ C.toProof) h_max (T.map blockToSpecEmb)
      cur (votes.map voteToSpecEmb) (support_votes.map voteToSpecEmb) s (Block.toSpec B))
    (DecoupledConsensusModel.Protocol.goldfish_eligible E (fun C => (σ C).toProof) h_max T cur
      votes support_votes s B))

/-- Record member `targets_under`: whether `vote` supports `B` in `T`, the spec's
    `Protocol.targets_under` when it answers, and `DecoupledConsensusModel.Protocol.targets_under`
    when it raises (`orVocabulary`). -/
def targets_under (T : Finset (DecoupledConsensusModel.Block V))
    (B : DecoupledConsensusModel.Block V) (vote : DecoupledConsensusModel.GoldfishVote V) :
    DC.NDRE Bool :=
  successOutcomes (orVocabulary
    (Protocol.targets_under (T.map blockToSpecEmb) (Block.toSpec B) (GoldfishVote.toSpec vote))
    (DecoupledConsensusModel.Protocol.targets_under T B vote))

/-- Record member `goldfish_fork_choice`: the Goldfish fork choice from `anchor` through `tree`, the
    spec's `Protocol.goldfish_fork_choice` when it answers, and
    `DecoupledConsensusModel.Protocol.goldfish_fork_choice` when it raises (`orVocabulary`). -/
def goldfish_fork_choice (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (anchor : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes (orVocabulary
    (Except.map Block.toProof
      (Protocol.goldfish_fork_choice (fun C => σ C.toProof) h_max (T.map blockToSpecEmb) cur
        (Block.toSpec anchor) (tree.map blockToSpecEmb) (votes.map voteToSpecEmb)
        (support_votes.map voteToSpecEmb) s))
    (DecoupledConsensusModel.Protocol.goldfish_fork_choice E (fun C => (σ C).toProof) h_max T cur
      anchor tree votes support_votes s))

/-- Record member `get_head_in_tree_with_layer`: the spec's `Protocol.get_head_in_tree_with_layer`,
    the fork-choice head of `st` in `tree` at slot `s` with its saved grades read from `c`; there is
    no outcome when the routine fails. -/
def get_head_in_tree_with_layer (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V)
    (tree : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes (Except.map Block.toProof
    (Protocol.get_head_in_tree_with_layer (Config.toSpec E hc unreadHeightConfig)
      { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round
          (st.contractOfImage c) ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        (tree.map st.blockOfImageEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s))

/-- Record member `viable_tree`: the spec's `Protocol.viable_tree`, the blocks of `T` that are
    descendants of `F` and viable for `h_max`. -/
def viable_tree (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V)
    (F : DecoupledConsensusModel.Block V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) : Finset (DecoupledConsensusModel.Block V) :=
  (Protocol.viable_tree (fun C => σ C.toProof) (Block.toSpec F) h_max (T.map blockToSpecEmb)).image
    Block.toProof

/-- Record member `no_second_vote_in`: the spec's `Protocol.no_second_vote_in`, whether every vote
    of `late` is `vote` itself or a vote of another validator. -/
def no_second_vote_in (late : Finset (DecoupledConsensusModel.GoldfishVote V))
    (vote : DecoupledConsensusModel.GoldfishVote V) : Bool :=
  Protocol.no_second_vote_in (late.map voteToSpecEmb) (GoldfishVote.toSpec vote)

/-- Record member `viable`: the spec's `Protocol.viable`, whether `B` or a descendant `W` of `B` in
    `T` has `h_max − 1 ≤ (σ W).h`. -/
def viable (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (B : DecoupledConsensusModel.Block V) : Bool :=
  Protocol.viable (fun C => σ C.toProof) h_max (T.map blockToSpecEmb) (Block.toSpec B)

/-- Record member `finalized_descendants`: the spec's `Protocol.finalized_descendants`, the blocks
    of `T` that are `F` or descendants of `F`. -/
def finalized_descendants (F : DecoupledConsensusModel.Block V)
    (T : Finset (DecoupledConsensusModel.Block V)) : Finset (DecoupledConsensusModel.Block V) :=
  (Protocol.finalized_descendants (Block.toSpec F) (T.map blockToSpecEmb)).image Block.toProof

/-- Record member `ghost_step`: the spec's `Protocol.ghost_step`, one step of the walk from `H`
    through `tree`; an outcome is the best eligible child of `H`, if there is one. -/
def ghost_step (tree : Finset (DecoupledConsensusModel.Block V))
    (score : DecoupledConsensusModel.Block V → ℕ) (eligible : DecoupledConsensusModel.Block V → Bool)
    (H : DecoupledConsensusModel.Block V) : DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes (Except.map (Option.map Block.toProof)
    (Protocol.ghost_step (tree.map blockToSpecEmb) (fun C => pure (score C.toProof))
      (fun C => pure (eligible C.toProof)) (Block.toSpec H)))

/-- Record member `get_filtered_block_tree_from`: the spec's `Protocol.get_filtered_block_tree_from`
    on `st` read through its tree (`Store.ofImage`), at the blocks of `st`'s tree read from `blocks`
    by `st.blockOfImage`. -/
def get_filtered_block_tree_from (st : Store V)
    (blocks : Finset (DecoupledConsensusModel.Block V)) :
    Finset (DecoupledConsensusModel.Block V) :=
  (Protocol.get_filtered_block_tree_from (Store.ofImage st) (blocks.map st.blockOfImageEmb)).image Block.toProof

/-- Record member `raw_participants`: the spec's `Protocol.raw_participants`, the validators with a
    vote in `votes`. -/
def raw_participants (votes : Finset (DecoupledConsensusModel.GoldfishVote V)) : Finset V :=
  Protocol.raw_participants (votes.map voteToSpecEmb)

/-- Record member `raw_supporters`: the supporters of `B` in slot `s`, the spec's
    `Protocol.raw_supporters` when it answers, and `DecoupledConsensusModel.Protocol.raw_supporters`
    when it raises (`orVocabulary`). -/
def raw_supporters (T : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) : DC.NDRE (Finset V) :=
  successOutcomes (orVocabulary
    (Protocol.raw_supporters (T.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (Block.toSpec B))
    (DecoupledConsensusModel.Protocol.raw_supporters T votes support_votes s B))

/-! ## The grades family: readers and projections -/

/-- Record member `toFG`: the identity, since the spec has one store type. -/
def toFG : Store V → Store V := id

/-- Record member `gv_T`: the blocks of `st`. -/
def gv_T (st : Store V) : Finset (DecoupledConsensusModel.Block V) :=
  st.T.image Block.toProof

/-- Record member `gv_timestamp_block`: the time at which `st` received each block, read at the
    block of its tree given by `st.blockOfImage`. -/
def gv_timestamp_block (st : Store V) :
    DecoupledConsensusModel.TimestampMap (DecoupledConsensusModel.Block V) :=
  fun B => st.timestamp_block (st.blockOfImage B)

/-- Record member `gv_tree`: the spec's `Protocol.get_filtered_block_tree` of `st` read through its
    tree (`Store.ofImage`), the tree the grades of `st` walk. -/
def gv_tree (st : Store V) : Finset (DecoupledConsensusModel.Block V) :=
  (Protocol.get_filtered_block_tree (Store.ofImage st)).image Block.toProof

/-- Record member `gv_sg_votes`: the SG votes of round `r` in `st`. -/
def gv_sg_votes (st : Store V) (r : Round) : Finset (DecoupledConsensusModel.Protocol.SGVote V) :=
  (st.sg_votes r).map Protocol.SGVote.toProofEmb

/-- Record member `gv_timestamp_sg_vote`: the time at which `st` received each SG vote. -/
def gv_timestamp_sg_vote (st : Store V) :
    DecoupledConsensusModel.TimestampMap (DecoupledConsensusModel.Protocol.SGVote V) :=
  fun u => st.timestamp_sg_vote (Protocol.SGVote.toSpec u)

/-- Record member `g0`: the grade-0 result of `fr`, if computed. -/
def g0 (fr : RoundGrades V) : Option (Option (DecoupledConsensusModel.Block V)) :=
  fr.g0.toProof

/-- Record member `g1`: the grade-1 result of `fr`, if computed. -/
def g1 (fr : RoundGrades V) : Option (Option (DecoupledConsensusModel.Block V)) :=
  fr.g1.toProof

/-- Record member `g2`: the grade-2 result of `fr`, if computed. -/
def g2 (fr : RoundGrades V) : Option (Option (DecoupledConsensusModel.Block V)) :=
  fr.g2.toProof

/-- Record member `round`: the round the saved grades `c` are aligned to. -/
def round (c : SavedGrades V) : Round := c.round

/-- Record member `cache_current`: the grades of the saved grades' own round. -/
def cache_current (c : SavedGrades V) : RoundGrades V := c.current

/-!
## The grades family: the grade contract and its reads

The record's contract type is the saved grades, and a read through a contract `c` reads the store
with its saved grades replaced by `c`.
-/

/-- Record member `clear`: whether `B` is compatible with the grade-0 block of `fr`; `true` when the
    grade-0 result is pending or was computed with no block. -/
def clear (fr : RoundGrades V) (B : DecoupledConsensusModel.Block V) : Bool :=
  DecoupledConsensusModel.Protocol.clear fr.toProof B

/-- Record member `read`: the spec's `Protocol.round_grade_read` of round `r` on the store `st` with
    its saved grades read from `c`, its grade-0 test given by `clear`; there is no outcome when the
    read fails. -/
def read (c : SavedGrades V) (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (r : Round) :
    DC.NDRE (DecoupledConsensusModel.Protocol.GradeRead V) :=
  successOutcomes (Except.map
    (fun g => { g.toProof with
      clear := clear (Protocol.round_grades
        { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) }
        r) })
    (Protocol.round_grade_read
      { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) }
      r))

/-- Record member `confirmationSG`: the spec's `Protocol.confirmation_candidate`, the SG candidate
    of `st`'s round on the store `st` with its saved grades read from `c`. The slot argument is not
    read. -/
def confirmationSG (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (_s : Slot) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes (Except.map (Option.map Block.toProof)
    (Protocol.confirmation_candidate (Config.toSpec E hc unreadHeightConfig)
      { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round
          (st.contractOfImage c) ((Config.toSpec E hc unreadHeightConfig).round_of st.s)) }))

/-- Record member `stableRoot`: `some` of the spec's `Protocol.round_stable_root`, the stable root
    of round `r` on the store `st` with its saved grades read from `c`; there is no outcome when the
    read fails. -/
def stableRoot (c : SavedGrades V) (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (r : Round) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes (Except.map (fun B => some B.toProof)
    (Protocol.round_stable_root
      { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) }
      r))

/-- Record member `currentSGVote`: the spec's `Protocol.currentSGVote`, the block a validator with
    store `st` votes for in SG given the grade read `g`. -/
def currentSGVote (st : Store V) (g : DecoupledConsensusModel.Protocol.GradeRead V) :
    DecoupledConsensusModel.Block V :=
  (Protocol.currentSGVote (Store.ofImage st) (gradeReadOfImage st g)).toProof

/-- Record member `contract_sgVote`: `currentSGVote st g`; the saved grades `c` are not read. -/
def contract_sgVote (_c : SavedGrades V) (st : Store V)
    (g : DecoupledConsensusModel.Protocol.GradeRead V) : DecoupledConsensusModel.Block V :=
  currentSGVote st g

/-- Record member `mkContract`: the initial saved grades `Protocol.initial_saved_grades`, whatever
    the four parts given. It has no faithful value, since saved grades cannot be recovered from four
    functions. -/
def mkContract
    (_rd : DecoupledConsensusModel.Env V → DecoupledConsensusModel.Protocol.HealConfig → Store V →
      Round → DecoupledConsensusModel.Protocol.GradeRead V)
    (_sv : Store V → DecoupledConsensusModel.Protocol.GradeRead V → DecoupledConsensusModel.Block V)
    (_sel : DecoupledConsensusModel.Env V → DecoupledConsensusModel.Protocol.HealConfig →
      Store V → Slot → Option (DecoupledConsensusModel.Block V))
    (_sr : DecoupledConsensusModel.Env V → DecoupledConsensusModel.Protocol.HealConfig →
      Store V → Round → Option (DecoupledConsensusModel.Block V)) : SavedGrades V :=
  Protocol.initial_saved_grades

/-- Record member `frameContract`: the identity on saved grades. -/
def frameContract : SavedGrades V → SavedGrades V := id

/-- Record member `frameGradeRead`: the same value as `read`, round `r`'s grade read from the saved
    grades `c` on `st`. -/
def frameGradeRead (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (r : Round) :
    DC.NDRE (DecoupledConsensusModel.Protocol.GradeRead V) :=
  read c E hc st r

/-- Record member `frameSGCandidate`: the same value as `confirmationSG`, the SG candidate of `st`'s
    round from the saved grades `c`. -/
def frameSGCandidate (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (s : Slot) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  confirmationSG c E hc st s

/-- Record member `frameStableRoot`: the same value as `stableRoot`, round `r`'s stable root from
    the saved grades `c` on `st`. -/
def frameStableRoot (c : SavedGrades V) (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (r : Round) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  stableRoot c E hc st r

/-! ## The grades family: the round schedule -/

/-- Record member `opening_slot`: the first slot of round `r`, `r * hc.R`. -/
def opening_slot (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : Round) : Slot :=
  r * hc.R

/-- Record member `round_of`: the round of slot `s`, `s / hc.R`. -/
def round_of (hc : DecoupledConsensusModel.Protocol.HealConfig) (s : Slot) : Round :=
  s / hc.R

/-- Record member `opening`: the time round `r` opens, the start of its first slot. -/
def opening (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (r : Round) : Time :=
  (Config.toSpec E hc unreadHeightConfig).opening r

/-- Record member `a`: round `r`'s attestation time, `6Δ` after the start of its first slot. -/
def a (hc : DecoupledConsensusModel.Protocol.HealConfig) (Δ : Time) (r : Round) : Time :=
  4 * Δ * ((r * hc.R : Slot) : Time) + 6 * Δ

/-- Record member `earlyOffset`: how many delays after the opening the first cutoff of grade `p`
    falls: `−3`, `−4`, `−5` for grades 0, 1, 2. -/
def earlyOffset (p : DecoupledConsensusModel.Protocol.Phase) : ℤ :=
  Protocol.Phase.earlyOffset (Protocol.Phase.toSpec p)

/-- Record member `lateOffset`: how many delays after the opening the second cutoff of grade `p`
    falls: `−3`, `−2`, `−1` for grades 0, 1, 2. -/
def lateOffset : DecoupledConsensusModel.Protocol.Phase → ℤ
  | .g0 => -3
  | .g1 => -2
  | .g2 => -1

/-- Record member `domainOffset`: how many delays after the opening grade `p` is computed: `1`, `0`,
    `−1` for grades 0, 1, 2. -/
def domainOffset : DecoupledConsensusModel.Protocol.Phase → ℤ
  | .g0 => 1
  | .g1 => 0
  | .g2 => -1

/-- Record member `early`: the first cutoff of round `r`'s grade `p`. -/
def early (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) : Time :=
  (Config.toSpec E hc unreadHeightConfig).early r (Protocol.Phase.toSpec p)

/-- Record member `late`: the second cutoff of round `r`'s grade `p`, `lateOffset p` delays after
    the opening of round `r`. -/
def late (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) : Time :=
  (Config.toSpec E hc unreadHeightConfig).opening r +
    lateOffset p * (Config.toSpec E hc unreadHeightConfig).Δ

/-- Record member `domain`: the time at which round `r`'s grade `p` is computed, `domainOffset p`
    delays after the opening of round `r`. -/
def domain (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) : Time :=
  (Config.toSpec E hc unreadHeightConfig).opening r +
    domainOffset p * (Config.toSpec E hc unreadHeightConfig).Δ

/-! ## The grades family: projections and frames -/

/-- Record member `gradeView`: the store `st` with its clock and slot set to `0`, its three
    confirmation records set to its finalized block, and its saved grades set to the initial saved
    grades. No grade routine reads these fields. -/
def gradeView (st : Store V) : Store V :=
  { st with t := 0, s := 0, live_confirmed := st.F, latest_confirmed := st.F,
            latest_stable := st.F, saved_grades := Protocol.initial_saved_grades }

/-- Record member `pendingFrame`: the round's grades with every result pending. -/
def pendingFrame : RoundGrades V := Protocol.pending_round_grades

/-- Record member `phaseResult`: the result of grade `p` in `fr`, if computed. -/
def phaseResult (fr : RoundGrades V) (p : DecoupledConsensusModel.Protocol.Phase) :
    Option (Option (DecoupledConsensusModel.Block V)) :=
  (Protocol.phaseResult fr (Protocol.Phase.toSpec p)).toProof

/-- Record member `putPhase`: the round's grades `fr` with grade `p`'s result set to `computed` of
    `result`. -/
def putPhase (fr : RoundGrades V) (p : DecoupledConsensusModel.Protocol.Phase)
    (result : Option (DecoupledConsensusModel.Block V)) : RoundGrades V :=
  match p with
  | .g0 => { fr with g0 := .computed (result.map Block.toSpec) }
  | .g1 => { fr with g1 := .computed (result.map Block.toSpec) }
  | .g2 => { fr with g2 := .computed (result.map Block.toSpec) }

/-- Record member `allClosed`: whether none of the three grade results of `fr` is pending. -/
def allClosed (fr : RoundGrades V) : Bool :=
  decide (fr.g0 ≠ .pending) && decide (fr.g1 ≠ .pending) && decide (fr.g2 ≠ .pending)

/-- Record member `readFrame`: the spec's `Protocol.round_grades` of round `r` on the store `st`
    with its saved grades `c` read through its tree (`Store.contractOfImage`). -/
def readFrame (c : SavedGrades V) (st : Store V) (r : Round) : RoundGrades V :=
  Protocol.round_grades { st with saved_grades := st.contractOfImage c } r

/-- Record member `cacheAtRound`: the spec's `Protocol.saved_round_grades`, the grades of round `r`
    in the saved grades `c`: the current ones, the next ones, or pending ones. -/
def cacheAtRound (c : SavedGrades V) (r : Round) : RoundGrades V :=
  Protocol.saved_round_grades c r

/-- Record member `alignRound`: the spec's `Protocol.advance_to_round`, the saved grades `c` brought
    to round `r`. -/
def alignRound (c : SavedGrades V) (r : Round) : SavedGrades V :=
  Protocol.advance_to_round c r

/-- Record member `clipGrade`: the spec's `Protocol.deepest_compatible_ancestor`, the deepest
    ancestor of `g`, `g` included, compatible with `F`. -/
def clipGrade (g F : DecoupledConsensusModel.Block V) : DecoupledConsensusModel.Block V :=
  (Protocol.deepest_compatible_ancestor (Block.toSpec g) (Block.toSpec F)).toProof

/-- Record member `clipResult`: the spec's `Protocol.make_result_compatible_with`, the result with
    its block replaced by its deepest ancestor compatible with `F`. -/
def clipResult (F : DecoupledConsensusModel.Block V)
    (result : Option (Option (DecoupledConsensusModel.Block V))) :
    Option (Option (DecoupledConsensusModel.Block V)) :=
  (Protocol.make_result_compatible_with (Block.toSpec F)
    (GradeResult.toSpec result)).toProof

/-- Record member `clipFrame`: the round's grades `fr` with each result's block replaced by its
    deepest ancestor whose image is compatible with `F` (`clipResultImage`). -/
def clipFrame (F : DecoupledConsensusModel.Block V) (fr : RoundGrades V) : RoundGrades V :=
  ⟨clipResultImage F fr.g0, clipResultImage F fr.g1, clipResultImage F fr.g2⟩

/-- Record member `clipCache`: the saved grades `c`, its round kept and the grades of both its
    rounds passed to `clipFrame F`. -/
def clipCache (F : DecoupledConsensusModel.Block V) (c : SavedGrades V) : SavedGrades V :=
  ⟨c.round, clipFrame F c.current, clipFrame F c.next⟩

/-- Record member `onPhaseTick`: the saved grades of the store the spec's `Protocol.update_grades`
    returns at time `t` on the store `st` with its saved grades replaced by `c`; there is no outcome
    when the routine fails. -/
def onPhaseTick (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (t : Time)
    (c : SavedGrades V) : DC.NDRE (SavedGrades V) :=
  successOutcomes (Except.map Store.saved_grades
    (Protocol.update_grades (Config.toSpec E hc unreadHeightConfig) (Provisional.toSpec E)
      { st with saved_grades := c } t))

/-! ## The grades family: the grade computation -/

/-- Record member `chain_up`: the spec's `Protocol.chain_up`, `B` and its ancestors at most `n`
    parent steps from `B`, deepest first. -/
def chain_up (n : ℕ) (B : DecoupledConsensusModel.Block V) :
    List (DecoupledConsensusModel.Block V) :=
  (Protocol.chain_up n (Block.toSpec B)).map Block.toProof

/-- Record member `chain_of`: the spec's `Protocol.chain_of`, `B` and all its ancestors, from `B` to
    the genesis block. -/
def chain_of (B : DecoupledConsensusModel.Block V) : List (DecoupledConsensusModel.Block V) :=
  (Protocol.chain_of (Block.toSpec B)).map Block.toProof

/-- Record member `deepest_clear`: the spec's `Protocol.deepest_clear`, the deepest ancestor of `C`,
    `C` included, that passes `test` and is a descendant of `floor` when `floor` is given; no
    `floor` is read as the genesis block. -/
def deepest_clear (floor : Option (DecoupledConsensusModel.Block V))
    (C : DecoupledConsensusModel.Block V) (test : DecoupledConsensusModel.Block V → Bool) :
    Option (DecoupledConsensusModel.Block V) :=
  (Protocol.deepest_clear ((floor.map Block.toSpec).getD .genesis) (Block.toSpec C)
    (fun B => test B.toProof)).map Block.toProof

/-- Record member `activePrefix`: the spec's `Protocol.activePrefix`, the deepest block of `tree`
    that is `root` or an ancestor of `root`, if any. -/
def activePrefix (tree : Finset (DecoupledConsensusModel.Block V))
    (root : DecoupledConsensusModel.Block V) : Option (DecoupledConsensusModel.Block V) :=
  (Protocol.activePrefix (tree.map blockToSpecEmb) (Block.toSpec root)).map Block.toProof

/-- Record member `token`: the spec's `Protocol.token`, the round and the confirmed root of `u`. -/
def token (u : DecoupledConsensusModel.Protocol.SGVote V) :
    DecoupledConsensusModel.Protocol.Token (Option DecoupledConsensusModel.BlockId) :=
  (Protocol.token (Protocol.SGVote.toSpec u)).toProof

/-- Record member `CleanFrom`: the spec's `Protocol.CleanFrom`, every two tokens of `raw` of one
    round, at round `k` or later, have one key. -/
def CleanFrom {Key : Type} (raw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (k : ℕ) :
    Prop :=
  Protocol.CleanFrom (raw.map tokenToSpecEmb) k

/-- Record member `Supports`: `DecoupledConsensusModel.Protocol.Supports`, whether some early token
    of the latest round covers `B`, the raw tokens are clean from its round, and every later late
    token covers `B`. -/
def Supports {Key Target : Type} (covers : Key → Target → Prop)
    (early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (B : Target) : Prop :=
  DecoupledConsensusModel.Protocol.Supports covers early late raw B

/-- Record member `Opposes`: `DecoupledConsensusModel.Protocol.Opposes`, whether a late token after
    every early one does not cover `B`, or two raw tokens of one round after every early one have
    different keys. -/
def Opposes {Key Target : Type} (covers : Key → Target → Prop)
    (early late raw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (B : Target) : Prop :=
  DecoupledConsensusModel.Protocol.Opposes covers early late raw B

/-- Record member `head_covers`: whether the root `H` names a descendant of `B` in `T`, the spec's
    `Protocol.head_covers` when it answers, and `DecoupledConsensusModel.Protocol.head_covers`
    (`false` there) when it raises (`orVocabulary`). -/
def head_covers (T : Finset (DecoupledConsensusModel.Block V))
    (B : DecoupledConsensusModel.Block V) (H : Option DecoupledConsensusModel.BlockId) :
    DC.NDRE Bool :=
  successOutcomes (orVocabulary
    (Protocol.head_covers (T.map blockToSpecEmb) (Block.toSpec B) (H.map BlockId.toSpec))
    (DecoupledConsensusModel.Protocol.head_covers T B H))

/-- Record member `localCovers`: whether `key` names a descendant of `B` in `st`'s tree, the spec's
    `Protocol.head_covers` over `st.T` when it answers, and
    `DecoupledConsensusModel.Protocol.localCovers` when it raises (`orVocabulary`). -/
def localCovers (st : Store V) (key : Option DecoupledConsensusModel.BlockId)
    (B : DecoupledConsensusModel.Block V) : DC.NDRE Bool :=
  successOutcomes (orVocabulary
    (Protocol.head_covers st.T (st.blockOfImage B) (key.map BlockId.toSpec))
    (DecoupledConsensusModel.Protocol.localCovers st.toProof.toHealing.gradeView key B))

/-- Record member `bodyReady`: the spec's `Protocol.bodyReady`, whether `u` names no root, or a
    block of `st` received before `t` and compatible with `F`. -/
def bodyReady (st : Store V) (F : DecoupledConsensusModel.Block V) (t : Time)
    (u : DecoupledConsensusModel.Protocol.SGVote V) : DC.NDRE Bool :=
  successOutcomes (Protocol.bodyReady st (st.blockOfImage F) t (Protocol.SGVote.toSpec u))

/-- Record member `rawInputs`: the spec's `Protocol.rawInputs`, `v`'s SG votes of the latest window
    stamped before `t`; there is no outcome when a vote of the window has no stamp. -/
def rawInputs (st : Store V) (eta r : Round) (t : Time) (v : V) :
    DC.NDRE (Finset (DecoupledConsensusModel.Protocol.SGVote V)) :=
  successOutcomes (Except.map (fun votes => votes.map Protocol.SGVote.toProofEmb)
    (Protocol.rawInputs st eta r t v))

/-- Record member `interpretedInputs`: the spec's `Protocol.interpretedInputs`, `v`'s SG votes of
    the latest window stamped before `t` and ready against `F`. -/
def interpretedInputs (st : Store V) (F : DecoupledConsensusModel.Block V) (eta r : Round)
    (t : Time) (v : V) : DC.NDRE (Finset (DecoupledConsensusModel.Protocol.SGVote V)) :=
  successOutcomes (Except.map (fun votes => votes.map Protocol.SGVote.toProofEmb)
    (Protocol.interpretedInputs st (st.blockOfImage F) eta r t v))

/-- Record member `rawView`: the spec's `Protocol.rawView`, the tokens of `v`'s SG votes of the
    latest window stamped before `t`. -/
def rawView (st : Store V) (eta r : Round) (t : Time) (v : V) :
    DC.NDRE (Finset (DecoupledConsensusModel.Protocol.Token
      (Option DecoupledConsensusModel.BlockId))) :=
  successOutcomes (Except.map (fun tokens => tokens.map Protocol.Token.toProofEmb)
    (Protocol.rawView st eta r t v))

/-- Record member `readyView`: the spec's `Protocol.readyView`, the tokens of `v`'s SG votes of the
    latest window stamped before `t` and ready against `F`. -/
def readyView (st : Store V) (F : DecoupledConsensusModel.Block V) (eta r : Round) (t : Time)
    (v : V) :
    DC.NDRE (Finset (DecoupledConsensusModel.Protocol.Token
      (Option DecoupledConsensusModel.BlockId))) :=
  successOutcomes (Except.map (fun tokens => tokens.map Protocol.Token.toProofEmb)
    (Protocol.readyView st (st.blockOfImage F) eta r t v))

/-- Record member `positive`: the spec's `Protocol.positive`, whether `v` supports `B` in round `r`
    with the cutoffs `t_0` and `t_1`. -/
def positive (st : Store V) (F : DecoupledConsensusModel.Block V) (eta r : Round)
    (t_0 t_1 : Time) (v : V) (B : DecoupledConsensusModel.Block V) : DC.NDRE Bool :=
  successOutcomes (Protocol.positive st (st.blockOfImage F) eta r t_0 t_1 v (st.blockOfImage B))

/-- Record member `opposing`: the spec's `Protocol.opposing`, whether `v` opposes `B` in round `r`
    with the cutoffs `t_0` and `t_1`. -/
def opposing (st : Store V) (F : DecoupledConsensusModel.Block V) (eta r : Round)
    (t_0 t_1 : Time) (v : V) (B : DecoupledConsensusModel.Block V) : DC.NDRE Bool :=
  successOutcomes (Protocol.opposing st (st.blockOfImage F) eta r t_0 t_1 v (st.blockOfImage B))

/-- Record member `gradeBool`: the spec's `Protocol.gradeBool`, the grade test of `B`: whether the
    supporters of `B` outweigh its opposers. -/
def gradeBool (E : DecoupledConsensusModel.Env V) (st : Store V)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t_0 t_1 : Time)
    (B : DecoupledConsensusModel.Block V) : DC.NDRE Bool :=
  successOutcomes (Protocol.gradeBool (Provisional.toSpec E) st (st.blockOfImage F) eta r t_0 t_1
    (st.blockOfImage B))

/-- Record member `freezeRoot`: the spec's `Protocol.freezeRoot`, the deepest block of `st`'s tree
    that passes the grade test, if any. -/
def freezeRoot (E : DecoupledConsensusModel.Env V) (st : Store V)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t_0 t_1 : Time) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes (Except.map (Option.map Block.toProof)
    (Protocol.freezeRoot (Provisional.toSpec E) st (st.blockOfImage F) eta r t_0 t_1))

/-- Record member `anchor`: the spec's `Protocol.anchor` of the grade-1 result `g1` on `st`, a
    pending result read as computed with no block (`fillResult`). The environment, the round
    schedule and the round are not read. -/
def anchor (_E : DecoupledConsensusModel.Env V)
    (_hc : DecoupledConsensusModel.Protocol.HealConfig) (st : Store V) (_r : Round)
    (g1 : Option (Option (DecoupledConsensusModel.Block V))) :
    DC.NDRE (DecoupledConsensusModel.Block V) :=
  successOutcomes (Except.map Block.toProof
    (Protocol.anchor (Store.ofImage st) (fillResult (gradeResultOfImage st g1))))

/-- Record member `grade2Block`: the spec's `Protocol.grade2Block`, the grade-2 candidate of `fr` on
    `st`, each pending result of `fr` read as computed with no block (`fillRound`). -/
def grade2Block (st : Store V) (fr : RoundGrades V) :
    DC.NDRE (Option (DecoupledConsensusModel.Block V)) :=
  successOutcomes (Except.map (Option.map Block.toProof)
    (Protocol.grade2Block (Store.ofImage st) (fillRound (st.roundGradesOfImage fr))))

end Member

end SpecDraftRecord
