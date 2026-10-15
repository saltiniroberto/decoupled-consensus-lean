module
public import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.Objects

@[expose] public section

/-!
# Latest votes and majority fork choice

The support round and support vote of a validator, the represented weight, the support weight, and
the majority walk, over a pool projection `Round → Finset (SGVote V)`. Counting is by weight over
all validators.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The greatest round `k` in `[max{0, r − η_SG}, r)` in which the pool holds a vote by `v` resolved
    in `T`, or `⊥` if there is none. -/
def latest_support_round (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) (r : Round) : Option Round :=
  ((latest_window η_SG r).filter (fun k =>
    holds_resolved_vote_by T (pool k) v)).getLast?


/-- The unique SG vote by `v` in its support round, or `⊥` when no round of the window holds a
    resolved vote by `v` or the selected round holds more than one distinct vote by `v`. -/
def latest_support_vote (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) (r : Round) : Option (SGVote V) :=
  match latest_support_round pool η_SG T v r with
  | none => none
  | some k => sole_vote? (pool k) v

/-- `v` is represented at round `r`: the expiry window holds a vote by `v`, resolved or not. -/
def represented (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (v : V) (r : Round) : Bool :=
  (latest_window η_SG r).any (fun k => holds_vote_by (pool k) v)

/-- The validators represented at round `r`, over all of `V`. -/
def represented_set (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (r : Round) : Finset V :=
  Finset.univ.filter (fun v => represented pool η_SG v r = true)

/-- The represented weight `W_r`. -/
def W_r (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (r : Round) : Nat :=
  E.electorate.weightOf (represented_set pool η_SG r)

/-! ## Support -/

/-- The vote's head resolves in `T` to a descendant of `B`; a timeout head or an unresolved head
    supports nothing. -/
def heads_under (T : Finset (Block V)) (B : Block V) (vote : SGVote V) : Bool :=
  match vote.confirmed with
  | none => false
  | some r =>
    match Block.find? T r with
    | some H => Block.preceq B H
    | none => false

/-- `v` supports `B` at round `r`: its `latest_support_vote` confirms a block `C` with `B ⪯ C`. -/
def supports (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) (v : V) : Bool :=
  match latest_support_vote pool η_SG T v r with
  | none => false
  | some vote => heads_under T B vote

/-- The validators that support `B` at round `r`. -/
def sgSupporters (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) : Finset V :=
  Finset.univ.filter (fun v => supports pool η_SG T r B v = true)

/-- The weight supporting `B` at round `r`. -/
def sg_support (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) : Nat :=
  E.electorate.weightOf (sgSupporters pool η_SG T r B)

/-! ## The majority walk -/

/-- The walk `ghost` from `anchor` over `tree` with `sg_support` as the score and a strict majority
    of `W_r` as the eligibility test. -/
def majority_fork_choice (E : Env V) (pool : Round → Finset (SGVote V))
    (η_SG : Round) (T : Finset (Block V)) (anchor : Block V)
    (tree : Finset (Block V)) (r : Round) : Block V :=
  let total := W_r E pool η_SG r
  let score := sg_support E pool η_SG T r
  Protocol.ghost anchor tree score (fun B => decide (total < 2 * score B))

end Protocol
end DecoupledConsensusModel

end
