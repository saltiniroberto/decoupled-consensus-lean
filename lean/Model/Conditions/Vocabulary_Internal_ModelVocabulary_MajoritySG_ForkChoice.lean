import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.ForkChoice
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Majority SG fork choice

The support-round selection, support, represented weight and majority fork choice of the SG, over a
model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol

/-- The greatest round `k ∈ [max{0, r − η_SG}, r)` whose votes in `pool k` include a vote by `v`
    resolved in `T`, or `⊥` when there is none. -/
def Vocabulary.Protocol.latest_support_round (M : Record.Model V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) (r : Round) : Option Round :=
  ((M.latest_window η_SG r).filter (fun k =>
    holds_resolved_vote_by T (pool k) v)).getLast?

end

section
open DecoupledConsensusModel.Protocol

/-- The unique SG vote by `v` in its support round `latest_support_round`, or `⊥` when there is no
    support round or that round holds more than one distinct vote by `v`. -/
def Vocabulary.Protocol.latest_support_vote (M : Record.Model V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) (r : Round) : Option (SGVote V) :=
  match Restated.Vocabulary.Protocol.latest_support_round M pool η_SG T v r with
  | none => none
  | some k => sole_vote? (pool k) v

end

section
open DecoupledConsensusModel.Protocol

/-- `v` is represented at round `r`: some round of `[max{0, r − η_SG}, r)` holds a vote by `v` in
    `pool`, resolved or not. -/
def Vocabulary.Protocol.represented (M : Record.Model V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (v : V) (r : Round) : Bool :=
  (M.latest_window η_SG r).any (fun k => holds_vote_by (pool k) v)

end

section
open DecoupledConsensusModel.Protocol

/-- The validators represented at round `r`. -/
def Vocabulary.Protocol.represented_set (M : Record.Model V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (r : Round) : Finset V :=
  Finset.univ.filter (fun v => Restated.Vocabulary.Protocol.represented M pool η_SG v r = true)

end

section
open DecoupledConsensusModel.Protocol

/-- The weight of the validators represented at round `r`. -/
def Vocabulary.Protocol.W_r (M : Record.Model V) (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (r : Round) : Nat :=
  E.electorate.weightOf (Restated.Vocabulary.Protocol.represented_set M pool η_SG r)

end

section
open DecoupledConsensusModel.Protocol

/-- `v` supports `B` at round `r`: its `latest_support_vote` is a vote for a block `C ≠ ⊥` with
    `B ⪯ C`. -/
def Vocabulary.Protocol.supports (M : Record.Model V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) (v : V) : Bool :=
  match Restated.Vocabulary.Protocol.latest_support_vote M pool η_SG T v r with
  | none => false
  | some vote => heads_under T B vote

end

section
open DecoupledConsensusModel.Protocol

/-- The validators that support `B` at round `r`. -/
def Vocabulary.Protocol.sgSupporters (M : Record.Model V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) : Finset V :=
  Finset.univ.filter (fun v => Restated.Vocabulary.Protocol.supports M pool η_SG T r B v = true)

end

section
open DecoupledConsensusModel.Protocol

/-- The weight of the validators that support `B` at round `r`. -/
def Vocabulary.Protocol.sg_support (M : Record.Model V) (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) : Nat :=
  E.electorate.weightOf (Restated.Vocabulary.Protocol.sgSupporters M pool η_SG T r B)

end

section
open DecoupledConsensusModel.Protocol

/-- The outcomes of the walk `M.ghost` from `anchor` over `tree`, scored by `sg_support` at round
    `r` and descending only into a block whose doubled score exceeds `W_r`. -/
def Vocabulary.Protocol.majority_fork_choice (M : Record.Model V) (E : Env V) (pool : Round → Finset (SGVote V))
    (η_SG : Round) (T : Finset (Block V)) (anchor : Block V)
    (tree : Finset (Block V)) (r : Round) : DC.NDRE (Block V) :=
  let total := Restated.Vocabulary.Protocol.W_r M E pool η_SG r
  let score := Restated.Vocabulary.Protocol.sg_support M E pool η_SG T r
  M.ghost anchor tree score (fun B => decide (total < 2 * score B))

end

section
open DecoupledConsensusModel.Protocol

/-- `DecoupledConsensusModel.Protocol.latest_support_round` equals
    `Restated.Vocabulary.Protocol.latest_support_round` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.latest_support_round_vocabulary_eq (pool : Round → Finset (SGVote V)) (η_SG : Round) (T : Finset (Block V)) (v : V) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.latest_support_round (V := V) pool η_SG T v r = Restated.Vocabulary.Protocol.latest_support_round (V := V) Record.Model.vocabulary pool η_SG T v r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.latest_support_vote` equals
    `Restated.Vocabulary.Protocol.latest_support_vote` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.latest_support_vote_vocabulary_eq (pool : Round → Finset (SGVote V)) (η_SG : Round) (T : Finset (Block V)) (v : V) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.latest_support_vote (V := V) pool η_SG T v r = Restated.Vocabulary.Protocol.latest_support_vote (V := V) Record.Model.vocabulary pool η_SG T v r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.represented` equals `Restated.Vocabulary.Protocol.represented`
    at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.represented_vocabulary_eq (pool : Round → Finset (SGVote V)) (η_SG : Round) (v : V) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.represented (V := V) pool η_SG v r = Restated.Vocabulary.Protocol.represented (V := V) Record.Model.vocabulary pool η_SG v r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.represented_set` equals
    `Restated.Vocabulary.Protocol.represented_set` at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.represented_set_vocabulary_eq (pool : Round → Finset (SGVote V)) (η_SG : Round) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.represented_set (V := V) pool η_SG r = Restated.Vocabulary.Protocol.represented_set (V := V) Record.Model.vocabulary pool η_SG r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.W_r` equals `Restated.Vocabulary.Protocol.W_r` at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.W_r_vocabulary_eq (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.W_r (V := V) E pool η_SG r = Restated.Vocabulary.Protocol.W_r (V := V) Record.Model.vocabulary E pool η_SG r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.supports` equals `Restated.Vocabulary.Protocol.supports` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.supports_vocabulary_eq (pool : Round → Finset (SGVote V)) (η_SG : Round) (T : Finset (Block V)) (r : Round) (B : Block V) (v : V) :
    _root_.DecoupledConsensusModel.Protocol.supports (V := V) pool η_SG T r B v = Restated.Vocabulary.Protocol.supports (V := V) Record.Model.vocabulary pool η_SG T r B v :=
  rfl

/-- `DecoupledConsensusModel.Protocol.sgSupporters` equals `Restated.Vocabulary.Protocol.sgSupporters`
    at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.sgSupporters_vocabulary_eq (pool : Round → Finset (SGVote V)) (η_SG : Round) (T : Finset (Block V)) (r : Round) (B : Block V) :
    _root_.DecoupledConsensusModel.Protocol.sgSupporters (V := V) pool η_SG T r B = Restated.Vocabulary.Protocol.sgSupporters (V := V) Record.Model.vocabulary pool η_SG T r B :=
  rfl

/-- `DecoupledConsensusModel.Protocol.sg_support` equals `Restated.Vocabulary.Protocol.sg_support` at
    the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.sg_support_vocabulary_eq (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round) (T : Finset (Block V)) (r : Round) (B : Block V) :
    _root_.DecoupledConsensusModel.Protocol.sg_support (V := V) E pool η_SG T r B = Restated.Vocabulary.Protocol.sg_support (V := V) Record.Model.vocabulary E pool η_SG T r B :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.majority_fork_choice` has the
    single outcome `DecoupledConsensusModel.Protocol.majority_fork_choice`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.majority_fork_choice_vocabulary_eq (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round) (T : Finset (Block V)) (anchor : Block V) (tree : Finset (Block V)) (r : Round) :
    Restated.Vocabulary.Protocol.majority_fork_choice (V := V) Record.Model.vocabulary E pool η_SG T anchor tree r =
      pure (_root_.DecoupledConsensusModel.Protocol.majority_fork_choice (V := V) E pool η_SG T anchor tree r) :=
  rfl

end

end DecoupledConsensusModel.Sts.Restated
