import Proofs.Instance.Objects
import Proofs.Instance.Equalities.ForkChoice
import Spec
import Model.Vocabulary

/-!
# Equalities for the grade routines

Each theorem `toProof_<member>` says that the `DecoupledConsensusModel` routine filling one member
of the grades family of the record, applied to the `toProof` images of the spec's data, equals the
image of the spec's routine at `Config.toSpec E hc cfg`. The members `clipGrade`, `clipResult`,
`clipFrame`, `clipCache`, `readFrame`, `activePrefix`, `gv_timestamp_block`, `gv_tree` and
`currentSGVote` have no theorem here: `Block.toProof` is not injective, and their equality does not
hold for every store and block.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open Spec

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The schedule of the rounds -/

/-- The record's member `round_of`: the round of slot `s` under `hc` is the round of `s` under
    `Config.toSpec E hc cfg`, for every `E` and `cfg`. -/
theorem toProof_round_of (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (s : Slot) :
    hc.round_of s = (Config.toSpec E hc cfg).round_of s := rfl

/-- The record's member `opening`: the time round `r` opens under `E` and `hc` is the spec's
    `Config.opening r` at `Config.toSpec E hc cfg`, for every `cfg`. -/
theorem toProof_opening (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (r : Round) :
    DecoupledConsensusModel.Protocol.opening E hc r = (Config.toSpec E hc cfg).opening r := rfl

omit [DecidableEq V] [Fintype V] in
/-- The record's member `earlyOffset`: the offset of the first cutoff of the image of phase `p` is
    the spec's offset of `p`'s first cutoff. -/
theorem toProof_earlyOffset (p : Protocol.Phase) :
    p.toProof.earlyOffset = Protocol.Phase.earlyOffset p := by
  cases p <;> rfl

/-- The record's member `early`: the first cutoff of round `r`'s result of the image of phase `p`
    under `E` and `hc` is the spec's `Config.early r p` at `Config.toSpec E hc cfg`, for every
    `cfg`. -/
theorem toProof_early (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (r : Round) (p : Protocol.Phase) :
    DecoupledConsensusModel.Protocol.early E hc r p.toProof =
      (Config.toSpec E hc cfg).early r p := by
  unfold DecoupledConsensusModel.Protocol.early Config.early
  rw [toProof_earlyOffset]
  rfl

/-! ## A round's grades and the saved grades -/

omit [DecidableEq V] [Fintype V] in
/-- The record's member `phaseResult`: the result of the image of phase `p` in the image of the
    round's grades `g` is the image of the spec's `Protocol.phaseResult g p`. -/
theorem toProof_phaseResult (g : RoundGrades V) (p : Protocol.Phase) :
    DecoupledConsensusModel.Protocol.phaseResult g.toProof p.toProof =
      (Protocol.phaseResult g p).toProof := by
  cases p <;> rfl

omit [DecidableEq V] [Fintype V] in
/-- The record's member `cacheAtRound`: the grades of round `r` in the image of the saved grades `c`
    are the image of the spec's `Protocol.saved_round_grades c r`. -/
theorem toProof_cacheAtRound (c : SavedGrades V) (r : Round) :
    DecoupledConsensusModel.Protocol.cacheAtRound c.toProof r =
      (Protocol.saved_round_grades c r).toProof := by
  unfold DecoupledConsensusModel.Protocol.cacheAtRound Protocol.saved_round_grades
  simp only [SavedGrades.toProof_round, SavedGrades.toProof_current, SavedGrades.toProof_next]
  split_ifs <;> rfl

/-! ## Tokens -/

omit [DecidableEq V] [Fintype V] in
/-- The record's member `token`: the token of the image of the SG vote `u` is the image of `u`'s
    token. -/
theorem toProof_token (u : Protocol.SGVote V) :
    DecoupledConsensusModel.Protocol.token u.toProof = (Protocol.token u).toProof := rfl

/-- The record's member `CleanFrom`, at the key type `Option BlockId`: `CleanFrom` holds of the
    image of `raw` from round `r` exactly when it holds of `raw` from round `r`. -/
theorem toProof_CleanFrom (raw : Finset (Protocol.Token (Option BlockId))) (r : Nat) :
    DecoupledConsensusModel.Protocol.CleanFrom (raw.map Protocol.Token.toProofEmb) r ↔
      Protocol.CleanFrom raw r := by
  have hround : ∀ x : Protocol.Token (Option BlockId), x.toProof.round = x.round := fun _ => rfl
  have hkey : ∀ x y : Protocol.Token (Option BlockId),
      x.toProof.key = y.toProof.key ↔ x.key = y.key := fun x y =>
    (Option.map_injective BlockId.toProof_injective).eq_iff
  simp only [DecoupledConsensusModel.Protocol.CleanFrom, Protocol.CleanFrom, Finset.forall_mem_map,
    Protocol.Token.coe_toProofEmb, hround, hkey]

/-! ## Chains of ancestors -/

omit [DecidableEq V] [Fintype V] in
/-- The record's member `chain_up`: `DecoupledConsensusModel.Protocol.chain_up n` of the image of
    `B` is the images, in order, of the spec's `Protocol.chain_up n B`. -/
theorem toProof_chain_up (n : Nat) (B : Block V) :
    DecoupledConsensusModel.Protocol.chain_up n B.toProof =
      (Protocol.chain_up n B).map Block.toProof := by
  induction n generalizing B with
  | zero => rfl
  | succ n ih =>
    cases B with
    | genesis => rfl
    | node p s r votes support ats proposer =>
      simp [DecoupledConsensusModel.Protocol.chain_up, Protocol.chain_up, Block.toProof,
        DecoupledConsensusModel.Block.parent?, Block.parent?, Id.run, ih, Option.value, pure]

omit [DecidableEq V] [Fintype V] in
/-- The record's member `chain_of`: `DecoupledConsensusModel.Protocol.chain_of` of the image of `B`
    is the images, in order, of the spec's `Protocol.chain_of B`. -/
theorem toProof_chain_of (B : Block V) :
    DecoupledConsensusModel.Protocol.chain_of B.toProof =
      (Protocol.chain_of B).map Block.toProof := by
  rw [DecoupledConsensusModel.Protocol.chain_of, Block.toProof_depth, toProof_chain_up]
  rfl

/-! ## The readers of the grade view -/

omit [Fintype V] in
/-- The record's member `gv_T`: the blocks of the grade view of the image of `st` are the images of
    the blocks of `st.T`. -/
theorem toProof_gv_T (st : Store V) :
    st.toProof.toHealing.gradeView.T = st.T.image Block.toProof := rfl

omit [Fintype V] in
/-- The record's member `gv_sg_votes`: the SG votes of round `r` in the grade view of the image of
    `st` are the images of `st`'s SG votes of round `r`. -/
theorem toProof_gv_sg_votes (st : Store V) (r : Round) :
    st.toProof.toHealing.gradeView.sg_votes r = (st.sg_votes r).map Protocol.SGVote.toProofEmb :=
  toProof_sgs_sg_votes st r

omit [Fintype V] in
/-- The record's member `gv_timestamp_sg_vote`: the grade view of the image of `st` stamps the SG
    vote `u` as `st` stamps its spec form. -/
theorem toProof_gv_timestamp_sg_vote (st : Store V)
    (u : DecoupledConsensusModel.Protocol.SGVote V) :
    st.toProof.toHealing.gradeView.timestamp_sg_vote u =
      st.timestamp_sg_vote (Protocol.SGVote.toSpec u) := rfl
