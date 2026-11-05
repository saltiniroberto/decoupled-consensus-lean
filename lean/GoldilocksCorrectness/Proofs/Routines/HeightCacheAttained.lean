module
public import GoldilocksCorrectness.Statements.Routines.HeightCacheAttainedDefs
public import GoldilocksCorrectness.Proofs.Routines.Wiring
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.Node

@[expose] public section

/-!
# What each node routine does to `HeightCacheAttained`

`HeightCacheAttained S` (`Statements/Routines/HeightCacheAttainedDefs.lean`): some block of the
tree `S.T` has the chain-state height `S.h_max`. This file proves that the node state a validator
starts from satisfies it of its FG state (`initial_heightCacheAttained`), that accepting a block
the tree does not hold keeps it (`fg_on_block_heightCacheAttained`), and that every node routine
that writes a node state keeps it: `on_block`, `on_attestation`, `on_ac_message`,
`propose_block`, `attest`, `record_awake`, `wake`, `tick`, and the wiring's dispatch of a
delivered object `Goldilocks.Sts.receive`. `HeightCacheAttained.of_frame` carries it to an FG
state with the same tree, chain states and cache `h_max`.

The one routine that writes `h_max` is the finality update, which sets it to the greater of
itself and the chain-state height it reads; accepting a block runs it on the chain state the
block has just been given, so the cache is the old witness's height or the new block's.

They read the node routines and node states alone: no execution.

Added for the record migration, step L1.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (HeightCacheAttained)

section

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- `HeightCacheAttained` transfers to an FG state with the same tree, the same chain states and
the same cache `h_max`.

The variables:
- `S`, `S'`: the two FG states.

Read aloud: a step that writes neither the tree, nor the chain states, nor `h_max` keeps the
cache the height of a block of the tree. -/
theorem HeightCacheAttained.of_frame {S S' : FGState V} (hT : S'.T = S.T) (hσ : S'.σ = S.σ)
    (hm : S'.h_max = S.h_max) (h : HeightCacheAttained S) : HeightCacheAttained S' := by
  obtain ⟨B, hB, hBh⟩ := h
  exact ⟨B, hT ▸ hB, by rw [hσ, hm]; exact hBh⟩

omit [Fintype V] in
/-- The node state a validator starts from satisfies `HeightCacheAttained` of its FG state: the
tree holds the genesis block alone, whose chain state is the initial one, of height `1`, and the
cache `h_max` is `1`.

The variables:
- `C`: the parameters; `v`: the validator.

Read aloud: at the start, the cache `h_max` is the genesis block's chain-state height. -/
theorem initial_heightCacheAttained (C : Config) (v : V) :
    HeightCacheAttained (initial C v).S :=
  ⟨Block.genesis, Finset.mem_singleton_self _, rfl⟩

section

variable [RootOrder]

/-- Accepting a block `B` the tree does not hold keeps `HeightCacheAttained`. The new tree is the
old one with `B`; `B` gets its chain state, and the finality update sets `h_max` to the greater of
the old cache and `B`'s chain-state height. When `B`'s height is the greater, `B` is the witness;
otherwise the old witness is, its chain state kept because it is not `B`.

The hypothesis `B ∉ S.T` is needed: a block already in the tree that is the only witness gets its
chain state rewritten, and the new chain state may be of a smaller height. `on_block` supplies it,
since `block_admissible` refuses a block whose root a block of the tree has.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block.

Read aloud: accepting a new block keeps the cache `h_max` the chain-state height of some block of
the tree. -/
theorem fg_on_block_heightCacheAttained (C : Config) (S : FGState V) (B : Block V)
    -- the tree of `S` does not hold `B`
    (hB : B ∉ S.T)
    -- some block of the tree of `S` has the chain-state height `S.h_max`
    (hS : HeightCacheAttained S) :
    HeightCacheAttained (fg_on_block C S B) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef]
  obtain ⟨h1, h2, -⟩ := fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))
  obtain ⟨-, h4⟩ := fg_on_attestations_caches B.attestations (update_finality S₁ (S₁.σ B))
  obtain ⟨u1, u2, -⟩ := update_finality_keeps S₁ (S₁.σ B)
  unfold HeightCacheAttained
  rw [h1, h2, h4, u1, u2, update_finality_h_max]
  obtain ⟨B₀, hB₀, hh⟩ := hS
  have hne : B₀ ≠ B := fun he => hB (he ▸ hB₀)
  by_cases hle : S.h_max ≤ (S₁.σ B).h
  · refine ⟨B, Finset.mem_union_right _ (Finset.mem_singleton_self B), ?_⟩
    rw [max_eq_right hle]
  · refine ⟨B₀, Finset.mem_union_left _ hB₀, ?_⟩
    show (Function.update S.σ B (state_transition C (S.σ B.parent) B) B₀).h =
      max S.h_max (S₁.σ B).h
    rw [Function.update_of_ne hne, max_eq_left (le_of_lt (Nat.lt_of_not_le hle)), hh]

/-- Receiving a block keeps `HeightCacheAttained` of the FG state. A refused block changes
nothing; an accepted block is not in the tree (`block_admissible_facts`), so
`fg_on_block_heightCacheAttained` applies.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block.

Read aloud: receiving a block keeps the cache `h_max` the chain-state height of some block of the
tree. -/
theorem on_block_heightCacheAttained (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained (on_block C P X n B).S := by
  rw [on_block_eq]
  split
  · rename_i hb
    exact fg_on_block_heightCacheAttained C n.S B (block_admissible_facts C P X n B hb).2.1 h
  · exact h

end

omit [Fintype V] in
/-- Receiving an attestation keeps `HeightCacheAttained` of the FG state: it writes the pool of
attestations only.

The variables:
- `n`: the node state; `a`: the attestation.

Read aloud: receiving an attestation keeps the cache `h_max` the chain-state height of some block
of the tree. -/
theorem on_attestation_heightCacheAttained (n : NodeState V) (a : Attestation V)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained (on_attestation n a).S := by
  simp only [on_attestation, Id.run]
  split
  · exact h
  · exact HeightCacheAttained.of_frame (fg_on_attestation_keeps n.S a).1
      (fg_on_attestation_keeps n.S a).2.1 (fg_on_attestation_caches n.S a).2 h

/-- Receiving a Goldfish vote keeps the FG state, so `HeightCacheAttained` of it.

The variables:
- `C`, `P`: the parameters and the values; `n`: the node state; `vote`: the vote.

Read aloud: receiving a Goldfish vote keeps the cache `h_max` the chain-state height of some block
of the tree. -/
theorem on_ac_message_heightCacheAttained (C : Config) (P : Provisional V) (n : NodeState V)
    (vote : GoldfishVote V)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained (on_ac_message C P n vote).S := by
  rw [on_ac_message_eq]
  exact h

/-- Waking keeps the FG state, so `HeightCacheAttained` of it.

The variables:
- `n`: the node state; `t`: the wake time.

Read aloud: waking keeps the cache `h_max` the chain-state height of some block of the tree. -/
theorem wake_heightCacheAttained (n : NodeState V) (t : Time)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained (wake n t).S := by
  rw [wake_eq]
  exact h

omit [DecidableEq V] [Fintype V] in
/-- Recording the time of a wake keeps the FG state, so `HeightCacheAttained` of it.

The variables:
- `n`: the node state; `t`: the time.

Read aloud: recording the time of a wake keeps the cache `h_max` the chain-state height of some
block of the tree. -/
theorem record_awake_heightCacheAttained (n : NodeState V) (t : Time)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained (record_awake n t).S := by
  rw [(record_awake_frame n t).1]
  exact h

section

variable [RootOrder]

/-- Every answer of the proposal keeps `HeightCacheAttained` of the FG state: it ends by receiving
the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: every answer of the proposal keeps the cache `h_max` the chain-state height of some
block of the tree. -/
theorem propose_block_heightCacheAttained (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    DREBPost (propose_block C P X n) (fun n' => HeightCacheAttained n'.S) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_heightCacheAttained C P X n _ h)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the attestation duty keeps `HeightCacheAttained` of the FG state: it writes
the anti-slashing record, and may receive its own attestation.

The variables:
- `C`: the parameters; `n`: the node state.

Read aloud: every answer of the attestation duty keeps the cache `h_max` the chain-state height of
some block of the tree. -/
theorem attest_heightCacheAttained (C : Config) (n : NodeState V)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    DREBPost (attest C n) (fun n' => HeightCacheAttained n'.S) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure h
    | exact DREBPost.pure (on_attestation_heightCacheAttained _ _ h)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick keeps `HeightCacheAttained` of the FG state: the wake record,
the clock and the tick of the available chain keep the FG state, and the proposal and the
attestation, when they run, keep it.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: every answer of the tick keeps the cache `h_max` the chain-state height of some block
of the tree. -/
theorem tick_heightCacheAttained (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (t : Time)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    DREBPost (tick C P X n t) (fun n' => HeightCacheAttained n'.S) := by
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : HeightCacheAttained
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).S :=
    record_awake_heightCacheAttained n t h
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (propose_block_heightCacheAttained C P X _ hq) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_heightCacheAttained C n₄ h₄) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_heightCacheAttained C _ hq) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

/-- The wiring's dispatch of a delivered object keeps `HeightCacheAttained` of the FG state.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object.

Read aloud: receiving any object keeps the cache `h_max` the chain-state height of some block of
the tree. -/
theorem receive_heightCacheAttained (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (o : NamedObject V)
    -- some block of `n`'s tree has the chain-state height `n.S.h_max`
    (h : HeightCacheAttained n.S) :
    HeightCacheAttained (Goldilocks.Sts.receive C P X n o).S := by
  cases o with
  | block B => exact on_block_heightCacheAttained C P X n B h
  | gfVote vote => exact on_ac_message_heightCacheAttained C P n vote h
  | attest a => exact on_attestation_heightCacheAttained n a h

end

end

end GoldilocksCorrectness.Proofs.Routines
