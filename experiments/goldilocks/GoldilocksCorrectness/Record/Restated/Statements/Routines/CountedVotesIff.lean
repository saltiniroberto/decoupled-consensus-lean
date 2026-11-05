module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefsGoldilocks
public import GoldilocksCorrectness.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Statements.Routines.WalkDefs

@[expose] public section

/-!
# CountedVotesIff, over a model

The theorems of `GoldilocksCorrectness/Statements/Routines/TickDefs.lean` and
`GoldilocksCorrectness/Statements/Routines/WalkDefs.lean` over a model `M` whose facts `F` hold:
`countedVotes_iff` (the two sets of votes a Goldfish vote of slot `s'` counts are those counted with
the view freeze `C.t_ (s' − 1) + 3 · C.Δ`) and `earlyVoteOnceFor_iff` (one early vote for `B` is one
with the cutoff `C.t_ s' + 2 · C.Δ`). The definitions are those of `TickDefs.lean` and
`WalkDefs.lean` over the record; the two theorems hold by definition.

The recovery section at the end of the page states each landed theorem again, at the AC state
`n.A` and the record `fg_to_ac n.S` of a node state `n` whose tree of `fg_to_ac n.S` has no two
blocks sharing a root: the record's definitions read the resolution time of a vote as
`ResolvesAt`, which is the spec's `tau` under that hypothesis only (`goldilocks_resolvesAt`), so
the recovery takes it (`goldilocks_countedVotes`, `goldilocks_earlyVoteOnceFor`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- `CountedVotes` is `CountedVotesAt` at the view freeze `C.t_ (s' − 1) + 3 · C.Δ`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the configuration; `n`: the node state;
- `s'`: the slot of the vote; `votes`, `support_votes`: the two sets.

Read aloud: the two sets are the ones the Goldfish vote of slot `s'` counts exactly when they are
the ones counted with the view freeze `C.t_ (s' − 1) + 3 · C.Δ`. -/
theorem countedVotes_iff (C : Config) (n : M.N) (s' : Slot)
    (votes support_votes : Finset (GoldfishVote V)) :
    CountedVotes M C n s' votes support_votes ↔
      CountedVotesAt M n (C.t_ (s' - 1) + 3 * C.Δ) s' votes support_votes :=
  Iff.rfl

/-- `EarlyVoteOnceFor` is `EarlyVoteOnceAt` at the cutoff `C.t_ s' + 2 · C.Δ`.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the configuration; `n`: the node state;
- `s'`: the slot; `B`: the block; `v`: the validator.

Read aloud: `v` has one early vote for `B` exactly when it has one with the cutoff
`C.t_ s' + 2 · C.Δ`. -/
theorem earlyVoteOnceFor_iff (C : Config) (n : M.N) (s' : Slot) (B : Block V) (v : V) :
    EarlyVoteOnceFor M C n s' B v ↔ EarlyVoteOnceAt M n (C.t_ s' + 2 * C.Δ) s' B v :=
  Iff.rfl

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.countedVotes_iff`,
recovered from its record form at the spec's model, at the AC state `n.A` and the record
`fg_to_ac n.S` of every node state `n` whose tree of `fg_to_ac n.S` has no two blocks sharing a
root.

Read aloud: the landed `countedVotes_iff` holds at the AC state `n.A` and the record
`fg_to_ac n.S` of every node state `n` whose tree of `fg_to_ac n.S` has no two blocks sharing a
root, as the record's theorem at the spec's model. -/
theorem countedVotes_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (n : NodeState V), RootsNameBlocksIn (fg_to_ac n.S).tree →
      type_of% (@GoldilocksCorrectness.Statements.Routines.countedVotes_iff V _ C n.A
        (fg_to_ac n.S)) := by
  intro C n hRoots s' votes support_votes
  rw [goldilocks_countedVotes C n s' votes support_votes hRoots,
    goldilocks_countedVotesAt n _ s' votes support_votes hRoots]
  exact countedVotes_iff Model.goldilocks goldilocksFacts C n s' votes support_votes

/-- The landed `GoldilocksCorrectness.Statements.Routines.earlyVoteOnceFor_iff`,
recovered from its record form at the spec's model, at the AC state `n.A` and the record
`fg_to_ac n.S` of every node state `n` whose tree of `fg_to_ac n.S` has no two blocks sharing a
root.

Read aloud: the landed `earlyVoteOnceFor_iff` holds at the AC state `n.A` and the record
`fg_to_ac n.S` of every node state `n` whose tree of `fg_to_ac n.S` has no two blocks sharing a
root, as the record's theorem at the spec's model. -/
theorem earlyVoteOnceFor_iff_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (n : NodeState V), RootsNameBlocksIn (fg_to_ac n.S).tree →
      type_of% (@GoldilocksCorrectness.Statements.Routines.earlyVoteOnceFor_iff V _ C n.A
        (fg_to_ac n.S)) := by
  intro C n hRoots s' B v
  rw [goldilocks_earlyVoteOnceFor C n s' B v hRoots, goldilocks_earlyVoteOnceAt n _ s' B v hRoots]
  exact earlyVoteOnceFor_iff Model.goldilocks goldilocksFacts C n s' B v

end GoldilocksCorrectness.Record.Statements.Routines
