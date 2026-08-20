import Mathlib.Data.Finset.Max
import Spec.Consensus.Fig4SupportScores

/-!
# Figure 5 — Round-root functions called by `on_tick`

Definitions 13–15's root machinery: `get_proposal_root`, `get_lower_root`, `get_sg_root`,
`get_walk_root` and `get_action_root`. Each reads the stored round entries and computes
grades as needed; Figure 6's `on_tick` is the caller, at the scheduled instants its lines
name — the proposer's `get_proposal_root` at `t_r` (via `propose_block`, the draft's
undrafted Section 6), `get_sg_root` at the opening slot's vote time `t_r + Δ`, and
`get_action_root` at `a_r`.

The `-- line n` comments use Figure 5's own line numbering, in the draft as of 2026-08-19.
The routines appear in the figure's own order, which is already callee-first.

## "The deepest block in `G`"

The draft's two deepest-selections are over sets its Definition 12 argues lie on one chain
— two conflicting blocks cannot both hold direct support `m` — where the depth-maximal
element is unique. Over an arbitrary `Finset`, `deepest` keeps the depth-maximal elements
and lets the store's `ω` pick, so the routine is total without a chain hypothesis: the
old rendering's totalization, with the selection data read off the store instead of an
ambient instance.

## Two `Option` seams, both documented at the line

`Σ.root_proposal[r]` is `none` until a round-`r` opening block carrying a nonempty
proposal root is processed — line 13's `⊥` case (see `Fig2FinalityStore.lean` for the
strengthened write this reading rests on). And `Σ.sg_root[r]` is `Option`-valued, unset
before its scheduled write at `t_r + Δ`; `get_walk_root` is read at `a_r`, after it, so
the unset case is unreachable on schedule and falls back to the fork-choice root here.
-/

set_option autoImplicit false

namespace Consensus

variable {Validator Ω : Type}

/-- How many blocks `B`'s chain has, up to and including `B`. The draft's "deepest"
    selections compare blocks by chain position; this is that measure, off the ancestor
    list `Block` carries structurally. -/
def depth (B : Block Validator) : Nat := (ancestors B).length

section Roots
variable [DecidableEq Validator] [Electorate Validator] [Params] [Selection Validator Ω]

/-- The deepest block of a nonempty set: the depth-maximal elements, the store's `ω`
    picking among them through `Selection.select`. See the module header — on the one-chain
    sets the draft applies this to, the depth-maximal element is unique and the selection
    has no choice to make. -/
def deepest (S : Store Validator Ω) (s : Finset (Block Validator)) (h : s.Nonempty) :
    Block Validator :=
  (Selection.select S.ω (s.filter fun B => ∀ C ∈ s, depth C ≤ depth B)
    (by
      obtain ⟨B, hB, hmax⟩ := s.exists_max_image depth h
      exact ⟨B, Finset.mem_filter.mpr ⟨hB, hmax⟩⟩)).val

/-- `get_proposal_root(Σ, r)` (Figure 5, lines 1–5; Definition 13's producer side): what
    the round's opening proposer, at `t_r`, sets its opening block's proposal-root field
    to — the deepest block in `C(Σ)` with grade 2, or the current fork-choice root when no
    such block exists. -/
def getProposalRoot (S : Store Validator Ω) (r : Nat) : Block Validator := Id.run do
  let G := S.candidateTree.filter fun B => G2 S r B           -- line 2
  if hG : G.Nonempty then                                     -- line 3
    return deepest S G hG                                     -- line 4
  return S.forkChoiceRoot                                     -- line 5

/-- `get_lower_root(Σ, r)` (Figure 5, lines 6–10; Definition 14's `R_low`): the deepest
    block in `C(Σ)` with grade 3 strictly descending from the fork-choice root, or the
    fork-choice root itself when there is none. -/
def getLowerRoot (S : Store Validator Ω) (r : Nat) : Block Validator := Id.run do
  let G := S.candidateTree.filter fun B =>
    G3 S r B ∧ S.forkChoiceRoot ≺ B                           -- line 7
  if hG : G.Nonempty then                                     -- line 8
    return deepest S G hG                                     -- line 9
  return S.forkChoiceRoot                                     -- line 10

/-- `get_sg_root(Σ, r)` (Figure 5, lines 11–18; Definition 14): at the opening slot's vote
    time, derive the round's SG root. The validator accepts the round's root proposal
    `R_prop` exactly when `R_low ⪯ R_prop`, `R_prop ∈ C(Σ)` and `G1(R_prop)`; on acceptance
    the SG root is `R_prop`, otherwise `R_low` — the lower root is not retained. `on_tick`
    stores the result in `Σ.sg_root[r]`. -/
def getSGRoot (S : Store Validator Ω) (r : Nat) : Block Validator := Id.run do
  let Rlow := getLowerRoot S r                                -- line 12
  -- lines 13–15: `if Σ.root_proposal[r] = ⊥ then return R_low; R_prop ← Σ.root_proposal[r]`.
  -- The `⊥` case falls through to the closing `return R_low`.
  if hp : (S.rootProposal r).isSome then
    let Rprop := (S.rootProposal r).get hp
    if Rlow ⪯ Rprop ∧ Rprop ∈ S.candidateTree ∧ G1 S r Rprop then  -- line 16
      return Rprop                                            -- line 17
  return Rlow                                                 -- lines 14 and 18

/-- `get_walk_root(Σ, r)` (Figure 5, lines 19–23; Definition 14's fork-choice step): each
    Goldfish fork choice starts from the current fork-choice root `C`, and first moves to
    `R_SG = Σ.sg_root[r]` when `C ⪯ R_SG` — otherwise the step does not occur. An unset
    `Σ.sg_root[r]` — unreachable at the `a_r` read, which follows the `t_r + Δ` write —
    returns `C`. -/
def getWalkRoot (S : Store Validator Ω) (r : Nat) : Block Validator := Id.run do
  let C := S.forkChoiceRoot                                   -- line 20
  if hs : (S.sgRoot r).isSome then
    let Rsg := (S.sgRoot r).get hs
    if C ⪯ Rsg then                                           -- line 21
      return Rsg                                              -- line 22
  return C                                                    -- line 23, and the unset case

/-- `get_action_root(Σ, r)` (Figure 5, lines 24–29; Definition 15): at `a_r`, the root
    anchoring the round's SG and FG outputs — the walk root when it is in `C(Σ)` and either
    equals the fork-choice root or has grade 1, and the fork-choice root itself otherwise.
    A validator's own selection needs no external backing, while a round root adopted from
    others must still be viable and majority-backed at signing time. `on_tick` stores the
    result in `Σ.action_root[r]`. -/
def getActionRoot (S : Store Validator Ω) (r : Nat) : Block Validator := Id.run do
  let C := S.forkChoiceRoot                                   -- line 25
  let R := getWalkRoot S r                                    -- line 26
  if R ∈ S.candidateTree ∧ (R = C ∨ G1 S r R) then            -- line 27
    return R                                                  -- line 28
  return C                                                    -- line 29

end Roots

end Consensus
