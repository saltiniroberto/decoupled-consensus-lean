module
public import Mathlib.Data.Prod.Lex
public import Model.Vocabulary.Protocol.StoreBase
public import Model.Vocabulary.Protocol.Schedule
public import Model.Vocabulary.Protocol.ForkChoice.Views
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# Goldfish fork choice and store layers

The Goldfish score and walk, the SG and finality-gadget store layers, the viable tree,
`get_fg_root`, the filtered block tree, Goldfish eligibility and the Goldfish fork choice.
-/

section
/-! ## Goldfish fork choice -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

namespace VoteSetValid

end VoteSetValid

/-- The validators that equivocate in `votes`. -/
def raw_equivocators (votes : Finset (GoldfishVote V)) : Finset V :=
  Finset.univ.filter (fun v => equivocates votes v = true)

/-- The validators with a vote in `votes`. -/
def raw_participants (votes : Finset (GoldfishVote V)) : Finset V :=
  Finset.univ.filter (fun v => participates votes v = true)

/-- The number of validators with a vote in `votes`. -/
def raw_voters_count (votes : Finset (GoldfishVote V)) : Nat :=
  (raw_participants votes).card

/-- The number of validators with a vote in `votes`; `E` and `s` are not read. -/
def voters_count (_E : Env V) (votes : Finset (GoldfishVote V)) (_s : Slot) : Nat :=
  raw_voters_count votes

/-! ## Score -/

/-- Whether `vote`'s block, resolved by root in `T`, is a descendant of or equal to `B`; a vote that
    `T` does not resolve supports nothing. -/
def targets_under (T : Finset (Block V)) (B : Block V) (vote : GoldfishVote V) :
    Bool :=
  match Block.find? T vote.head with
  | some B' => decide (B'.slot ≤ vote.slot) && Block.preceq B B'
  | none => false

/-- The validators that do not equivocate in `votes` and have a slot-`s` vote in `support_votes`
    whose block is a descendant of, or equal to, `B` in `T`. -/
def raw_supporters (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    Finset V :=
  Finset.univ.filter (fun v =>
    equivocates votes v = false ∧
    ∃ vote ∈ votes_by support_votes v, vote.slot = s ∧ targets_under T B vote = true)

/-- The Goldfish score of `B`: the number of equivocators plus the number of supporters. -/
def raw_goldfish_score (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : Nat :=
  (raw_equivocators votes).card + (raw_supporters T votes support_votes s B).card

/-- The Goldfish score of `B`, `raw_goldfish_score`; `E` is not read. -/
def goldfish_score (_E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : Nat :=
  raw_goldfish_score T votes support_votes s B

/-! ## The walk -/

/-- The order of the walk: `outranks score B C` holds when `B` has a higher score than `C`, or an
    equal score and a greater root. -/
def outranks (score : Block V → Nat) (B C : Block V) : Bool :=
  decide (score C < score B) ||
    (decide (score C = score B) && decide (C.root < B.root))

/-- Whether no member of `children` outranks `B`. -/
def is_best_in (score : Block V → Nat) (children : Finset (Block V))
    (B : Block V) : Bool :=
  decide (∀ C ∈ children, outranks score C B = false)

/-- The child with the highest score, ties broken by the greater root; `none` on an empty set, or
    when two distinct children share both score and root. -/
def argmax? (score : Block V → Nat) (children : Finset (Block V)) :
    Option (Block V) :=
  pickUnique? children (is_best_in score children)

/-- The eligible children of `H` in `tree`: the members of `tree` whose parent is `H` and that pass
    `eligible`. -/
def ghost_children (tree : Finset (Block V)) (eligible : Block V → Bool)
    (H : Block V) : Finset (Block V) :=
  tree.filter (fun B => B.parent? = some H ∧ eligible B = true)

/-- One step of the walk: the best eligible child of `H`, or `none` when there is none. -/
def ghost_step (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) (H : Block V) : Option (Block V) :=
  argmax? score (ghost_children tree eligible H)

/-- The walk with fuel: repeat `ghost_step` from the current head, returning it when no eligible
    child remains or the fuel runs out. -/
def ghost_walk (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) : Nat → Block V → Block V
  | 0, H => H
  | n + 1, H =>
    match ghost_step tree score eligible H with
    | none => H
    | some C => ghost_walk tree score eligible n C

/-- `ghost(anchor, tree, score, eligible)`: descend from `anchor` through eligible children in
    `tree`, taking the highest score at each step, and stop where no child is eligible; the fuel is
    `tree.card`. -/
def ghost (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) : Block V :=
  ghost_walk tree score eligible tree.card anchor

end Protocol
end DecoupledConsensusModel
end

section

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Whether `late` holds no vote by `vote`'s validator other than `vote` itself. -/
def no_second_vote_in (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) :
    Bool :=
  decide (∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index)

end Protocol
end DecoupledConsensusModel
end

section
/-! ## SG votes -/

namespace DecoupledConsensusModel
namespace Protocol

/-- An SG vote `(v, r, C)`: validator `v`, round `r`, and the confirmed block `C` by root, or `⊥`. -/
structure SGVote (V : Type) where
  /-- The voting validator. -/
  val_index : V
  /-- The round of the vote. -/
  round : Round
  /-- The confirmed block, by root, or `⊥`. -/
  confirmed : Option BlockId
deriving DecidableEq, Repr

end Protocol
end DecoupledConsensusModel
end

section
/-! ## SG store -/

namespace DecoupledConsensusModel
namespace Protocol

/-- The SG store: the Goldfish store plus the processed SG votes of each round and their timestamps. -/
structure SGStore (V : Type) extends Protocol.GoldfishStore V where
  /-- `Σ.sg_votes[r]`: the processed round-`r` SG votes. -/
  sg_votes : Round → Finset (SGVote V)
  /-- The timestamps of the processed SG votes. -/
  timestamp_sg_vote : TimestampMap (SGVote V)

namespace SGStore

variable {V : Type} [DecidableEq V]

end SGStore

end Protocol
end DecoupledConsensusModel
end

section
/-! ## Latest votes and majority root -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Latest vote -/

/-- The expiry window `[max{0, r−η_SG}, r)`, in ascending order; empty at `r = 0`. -/
def latest_window (η_SG : Round) (r : Round) : List Round :=
  List.range' (r - η_SG) (min r η_SG)

end Protocol
end DecoupledConsensusModel
end

section
/-! ## Stored states and finality updates -/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)

/-! ## Justification events -/

/-- A justification event `(h_j, J.root)`, ordered lexicographically. -/
@[ext]
structure HeightId where
  /-- The justification height `h_j`. -/
  height : Height
  /-- The justified block's root `J.root`. -/
  id : BlockId
deriving DecidableEq, Repr

private theorem HeightId.rank_injective :
    Function.Injective (fun value : HeightId => (value.height, value.id)) := by
  intro left right equal
  exact HeightId.ext (congrArg Prod.fst equal) (congrArg Prod.snd equal)

/-- The lexicographic order on `(h_j, J.root)`. -/
instance : LinearOrder HeightId :=
  LinearOrder.lift'
    (fun value => toLex (value.height, value.id))
    (fun _ _ equal => by exact HeightId.rank_injective (toLex.injective equal))

/-! ## The store -/

/-- The finality-gadget store: the SG store plus the chain state of each block and the store's `F`,
    `J`, `h_j` and `h_max`. -/
structure FGStore (V : Type) extends toSG : Protocol.SGStore V where
  /-- `Σ.σ[B]`: the chain state after `B`, with `ChainState.initial` as the default. -/
  σ : Block V → ChainState V
  /-- `Σ.F`: the store's finalized block. -/
  F : Block V
  /-- `Σ.J`: the store's justified block. -/
  J : Block V
  /-- `Σ.h_j`: the height of `Σ.J`. -/
  h_j : Height
  /-- `Σ.h_max`: the running maximum chain-state height. -/
  h_max : Height

namespace FGStore

variable {V : Type} [DecidableEq V]

end FGStore

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Derived sets -/

/-- The blocks of `T` that are descendants of, or equal to, `F`. -/
def finalized_descendants (F : Block V) (T : Finset (Block V)) :
    Finset (Block V) :=
  T.filter (fun B => Block.preceq F B = true)

/-- Whether `B` is viable: some block `W` of `T` with `B ⪯ W` has chain-state height at least
    `h_max − 1`. -/
def viable (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (B : Block V) : Bool :=
  decide (∃ W ∈ T, Block.Preceq B W ∧ h_max - 1 ≤ (σ W).h)

/-- `viable_tree(Σ)`: the viable blocks of `T` that are descendants of, or equal to, `F`. -/
def viable_tree (σ : Block V → ChainState V) (F : Block V) (h_max : Height)
    (T : Finset (Block V)) : Finset (Block V) :=
  (finalized_descendants F T).filter (fun B => viable σ h_max T B = true)

/-- `get_fg_root(Σ)`: `Σ.J` when `Σ.h_max = Σ.h_j + 1`, `Σ.F` otherwise. -/
def get_fg_root (st : FGStore V) : Block V :=
  if st.h_max = st.h_j + 1 then st.J else st.F

end Protocol
end DecoupledConsensusModel
end

section
/-! ## Fork choice -/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `get_filtered_block_tree_from(Σ, blocks)`: the viable tree computed within `blocks`, kept to the
    descendants of, or equal to, `get_fg_root(Σ)`. -/
def get_filtered_block_tree_from (st : FGStore V) (blocks : Finset (Block V)) :
    Finset (Block V) :=
  let root := get_fg_root st
  (viable_tree st.σ st.F st.h_max blocks).filter (fun B =>
    Block.preceq root B = true)

/-- `get_filtered_block_tree(Σ)`: `get_filtered_block_tree_from` over the whole processed tree
    `Σ.T`. -/
def get_filtered_block_tree (st : FGStore V) : Finset (Block V) :=
  get_filtered_block_tree_from st st.T

/-- `goldfish_eligible`: a block `B` is eligible when its parent's chain-state height is less than
    `h_max − 1`, or its Goldfish score is more than half the voter count, or its slot is the current
    slot `cur`. -/
def goldfish_eligible (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V) : Bool :=
  decide ((σ B.parent).h < h_max - 1) ||
    decide (Protocol.voters_count E votes s <
      2 * Protocol.goldfish_score E T votes support_votes s B) ||
    decide (B.slot = cur)

/-- `goldfish_fork_choice`: the walk `ghost` from `anchor` in `tree`, with the Goldfish score and
    `goldfish_eligible`. -/
def goldfish_fork_choice (E : Env V) (σ : Block V → ChainState V)
    (h_max : Height) (T : Finset (Block V)) (cur : Slot) (anchor : Block V)
    (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    Block V :=
  Protocol.ghost anchor tree
    (Protocol.goldfish_score E T votes support_votes s)
    (goldfish_eligible E σ h_max T cur votes support_votes s)

end Protocol
end DecoupledConsensusModel
end

end
