module
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# The AC pool invariant without its stamp bound

`PoolInv P A` is `VotesInv P A t` (`ACStore.lean`) without the bound of the vote stamps by `t`: the
pool is filed by slot and committee, and its votes are stamped. Every AC routine keeps it at any time;
the theorems are the landed `VotesInv` lemmas (`ACStore.lean`, `ACInterface.lean`, `ForkChoiceFacts.lean`,
`RevokeLocks.lean`, `Confirmation.lean`) with the bound removed. The clock-free part of the node
invariant (`NodeCore.lean`, `Node.lean`) reads the pool through it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (PoolKeyed PoolStamped)

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `PoolInv P A`: the pool of `A` is filed by slot and committee (`PoolKeyed`) and its votes are
stamped (`PoolStamped`); `VotesInv` without the stamp bound.

The variables:
- `P`: the provisional values; `A`: the AC state.

Read aloud: the pool is well filed and stamped. -/
def PoolInv (P : Provisional V) (A : ACState V) : Prop := PoolKeyed P A ∧ PoolStamped A

/-- `PoolInv` holds of an AC state with the same pool and vote stamps.

The variables:
- `P`: the provisional values; `A`, `A'`: the two AC states.

Read aloud: keeping the votes and the stamps keeps the pool invariant. -/
theorem PoolInv.of_keeps {P : Provisional V} {A A' : ACState V}
    (hk : KeepsVotes A A') (h : PoolInv P A) : PoolInv P A' := by
  obtain ⟨h1, h2, -⟩ := hk
  unfold PoolInv PoolKeyed PoolStamped
  rw [h1, h2]
  exact h

/-- The admission of a Goldfish vote at any time keeps `PoolInv`: a vote it files under `vote.slot`
has that slot and passed the committee test, and is stamped. `on_goldfish_vote_votesInv` without the
stamp bound.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time; `vote`: the
  vote.

Read aloud: admitting a vote keeps the pool well filed and stamped. -/
theorem on_goldfish_vote_poolInv (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) (h : PoolInv P A) : PoolInv P (on_goldfish_vote C P A t vote) := by
  rcases on_goldfish_vote_cases C P A t vote with he | ⟨hc, he⟩
  · rw [he]; exact h
  rw [he]
  obtain ⟨hK, hS⟩ := h
  refine ⟨fun s vote' hv' => ?_, fun s vote' hv' => ?_⟩
  · simp only [Function.update_apply] at hv'
    split at hv'
    · rename_i hs
      subst hs
      rcases List.mem_append.mp hv' with hv' | hv'
      · exact hK _ vote' hv'
      · rw [List.mem_singleton.mp hv']
        exact ⟨rfl, hc⟩
    · exact hK s vote' hv'
  · simp only [Function.update_apply] at hv' ⊢
    split
    · simp
    · split at hv'
      · rename_i hne hs
        subst hs
        rcases List.mem_append.mp hv' with hv' | hv'
        · exact hS _ vote' hv'
        · exact absurd (List.mem_singleton.mp hv') hne
      · exact hS s vote' hv'

/-- The AC state's admission of a block's votes, at any time, keeps `PoolInv`.
`ac_on_block_votesInv` without the stamp bound.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the time; `B`: the block.

Read aloud: admitting a block's votes keeps the pool well filed and stamped. -/
theorem ac_on_block_poolInv (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (B : Block V) (h : PoolInv P A) : PoolInv P (ac_on_block C P A t B) := by
  simp only [ac_on_block, Id.run]
  exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
    (fun A' => PoolInv P A') h
    (fun A' vote _ hA' => on_goldfish_vote_poolInv C P A' t vote hA')

section

variable [RootOrder]

/-- The revocation of the locks keeps "`PoolInv`, with the block stamps of `A₀`".
`revoke_locks_from` without the stamp bound.

The variables:
- `P`: the provisional values; `A₀`: the AC state whose block stamps are kept; `A`: the AC state;
  `Φ`: the frame; `t`: the time; `s`: the slot.

Read aloud: the revocation keeps the pool well filed and stamped, and the block stamps. -/
theorem revoke_locks_fromPool {P : Provisional V} {A₀ : ACState V} (A : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    (h : PoolInv P A ∧ A.timestamp_block = A₀.timestamp_block) :
    DREPost (revoke_locks P A Φ t s)
      (fun A' => PoolInv P A' ∧ A'.timestamp_block = A₀.timestamp_block) :=
  (revoke_locks_keepsVotes P A Φ t s).mono (fun _ hk => ⟨h.1.of_keeps hk, hk.2.2.trans h.2⟩)

/-- The confirmation update keeps "`PoolInv`, with the block stamps of `A₀`".
`update_confirmation_from` without the stamp bound.

The variables:
- `C`, `P`: the parameters and the values; `A₀`: the AC state whose block stamps are kept; `A`: the
  AC state; `Φ`: the frame; `t`: the time; `s`: the slot.

Read aloud: the confirmation update keeps the pool well filed and stamped, and the block stamps. -/
theorem update_confirmation_fromPool {P : Provisional V} {A₀ : ACState V} (C : Config)
    (A : ACState V) (Φ : Frame V) (t : Time) (s : Slot)
    (h : PoolInv P A ∧ A.timestamp_block = A₀.timestamp_block) :
    DREPost (update_confirmation C P A Φ t s)
      (fun A' => PoolInv P A' ∧ A'.timestamp_block = A₀.timestamp_block) :=
  (update_confirmation_keepsVotes C P A Φ t s).mono
    (fun _ hk => ⟨h.1.of_keeps hk, hk.2.2.trans h.2⟩)

/-- Every answer of the Goldfish vote duty, at any time, keeps `PoolInv` and the block stamps.
`goldfish_vote_votesInv` without the stamp bound.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time; `v`:
  the node's validator.

Read aloud: the vote duty keeps the pool well filed and stamped, and the block stamps. -/
theorem goldfish_vote_poolInv (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (h : PoolInv P A) :
    DREBPost (goldfish_vote C P A Φ t v)
      (fun A' => PoolInv P A' ∧ A'.timestamp_block = A.timestamp_block) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBPost.pure ⟨h, rfl⟩
    | exact DREBPost.pure ⟨on_goldfish_vote_poolInv C P A t _ h,
        on_goldfish_vote_timestamp_block C P A t _⟩
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The Goldfish vote duty keeps "`PoolInv`, with the block stamps of `A₀`".

The variables:
- `C`: the parameters; `A₀`: the AC state whose block stamps are kept; `A`: the AC state; `Φ`: the
  frame; `t`: the time; `v`: the node's validator.

Read aloud: the vote duty keeps the pool well filed and stamped, and `A₀`'s block stamps. -/
theorem goldfish_vote_fromPool {P : Provisional V} {A₀ : ACState V} (C : Config)
    (A : ACState V) (Φ : Frame V) (t : Time) (v : V)
    (h : PoolInv P A ∧ A.timestamp_block = A₀.timestamp_block) :
    DREBPost (goldfish_vote C P A Φ t v)
      (fun A' => PoolInv P A' ∧ A'.timestamp_block = A₀.timestamp_block) :=
  (goldfish_vote_poolInv C P A Φ t v h.1).mono (fun _ h' => ⟨h'.1, h'.2.trans h.2⟩)

/-- Every answer of the tick of the available chain, at any time, keeps `PoolInv` and the block
stamps. `ac_on_tick_votesInv` without the stamp bound.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time; `v`:
  the node's validator; `b`, `b'`: the two wake tests.

Read aloud: the available chain's tick keeps the pool well filed and stamped, and the block
stamps. -/
theorem ac_on_tick_poolInv (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) (h : PoolInv P A) :
    DREBPost (ac_on_tick C P A Φ t v b b')
      (fun A' => PoolInv P A' ∧ A'.timestamp_block = A.timestamp_block) := by
  simp only [ac_on_tick]
  repeat' first
    | exact DREBPost.pure ⟨h, rfl⟩
    | exact DREBPost.pure (by assumption)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind (DREBPost.liftM (revoke_locks_fromPool (A₀ := A) _ _ _ _
        ⟨h, rfl⟩)) (fun _ _ => ?_)
    | refine DREBPost.bind (goldfish_vote_fromPool (A₀ := A) _ _ _ _ _
        (by first | exact ⟨h, rfl⟩ | assumption)) (fun _ _ => ?_)
    | refine DREBPost.bind (DREBPost.liftM (update_confirmation_fromPool (A₀ := A) _ _ _ _ _
        (by first | exact ⟨h, rfl⟩ | assumption))) (fun _ _ => ?_)

end

end

end GoldilocksCorrectness.Proofs.Routines
