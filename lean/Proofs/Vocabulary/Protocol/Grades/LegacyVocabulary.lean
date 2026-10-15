module
public import Proofs.Vocabulary.Internal.ModelVocabulary.MajoritySG.ForkChoice
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Blocks
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Env
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Time
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

noncomputable section

/-!
# Grade batch vocabulary

The round batch of SG votes, the head tie-break, the batch order, and the definitions built on them
that the grade lemmas are stated in.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The batch of round `r`: the SG votes of round `r − 1`, and empty for round 0. -/
def round_batch (gv : GradeView V) (r : Round) : Finset (SGVote V) :=
  if r = 0 then ∅ else gv.sg_votes (r - 1)

/-- The tie-break on equal timestamps: the fixed root order, with `⊥` least. -/
def head_lt : Option BlockId → Option BlockId → Bool
  | none, none => false
  | none, some _ => true
  | some _, none => false
  | some left, some right => decide (left < right)


/-- The batch order: by timestamp, ties broken by head; an unstamped vote sorts last. -/
def batch_before (ts : TimestampMap (SGVote V)) (left right : SGVote V) : Bool :=
  match ts left, ts right with
  | none, none => head_lt left.confirmed right.confirmed
  | none, some _ => false
  | some _, none => true
  | some x, some y =>
    decide (x < y) || (decide (x = y) && head_lt left.confirmed right.confirmed)


/-- No member of `batch` comes before `u` in the batch order. -/
def is_first_in (ts : TimestampMap (SGVote V)) (batch : Finset (SGVote V))
    (u : SGVote V) : Bool :=
  decide (∀ w ∈ batch, batch_before ts w u = false)


/-- The first vote of `batch` under the batch order, or `none` on an empty set or when the order
    does not single one out. -/
def batch_first? (ts : TimestampMap (SGVote V)) (batch : Finset (SGVote V)) :
    Option (SGVote V) :=
  pickUnique? batch (is_first_in ts batch)

/-- `e_v`: the receipt time at which the batch first holds two of `v`'s votes with distinct
    confirmed blocks, the empty value included, read off the receipt-earliest vote and the earliest
    vote whose confirmed block differs from it. -/
def equivocation_instant (ts : TimestampMap (SGVote V))
    (batch : Finset (SGVote V)) : Occurrence :=
  match batch_first? ts batch with
  | none => none
  | some first =>
    match batch_first? ts (batch.filter (fun u => u.confirmed ≠ first.confirmed)) with
    | none => none
    | some second => ts second


/-- The per-validator batch summary `(C_v, t_v, e_v)`. -/
structure BatchSummary where
  /-- `C_v`: the confirmed block of `v`'s first resolved vote naming one, or `⊥`. -/
  C_v : Option BlockId
  /-- `t_v`: that vote's resolution time, or `+∞`. -/
  t_v : Occurrence
  /-- `e_v`: the receipt time at which the pool first holds two of `v`'s votes with distinct
      confirmed blocks, the empty value included, or `+∞`. -/
  e_v : Occurrence


/-- The batch summary of `v` in round `r`: `C_v` and `t_v` from `v`'s first resolved vote naming a
    block, or `(⊥, +∞)` when there is none, and `e_v` from the receipt times. -/
def summary (gv : GradeView V) (r : Round) (v : V) : BatchSummary :=
  let batch := Protocol.sg_votes_by (round_batch gv r) v
  let τ := Protocol.sg_resolution_time gv.T gv.timestamp_block gv.timestamp_sg_vote
  let headed := batch_first? τ (batch.filter (fun u =>
    u.confirmed.isSome ∧ Protocol.sg_resolved gv.T u = true))
  { C_v := headed.bind SGVote.confirmed
    t_v := headed.elim none τ
    e_v := equivocation_instant gv.timestamp_sg_vote batch }

/-! ## Support -/

/-- `direct_support(Σ, r, Γ_h, Γ_e, B) = w({v ∈ V: t_v < Γ_h, B ⪯ C_v, e_v ≥ Γ_e})`. -/
def direct_support (E : Env V) (gv : GradeView V) (r : Round) (Γ_h Γ_e : Time)
    (B : Block V) : Nat :=
  E.electorate.weightOf (Finset.univ.filter (fun v =>
    let s := summary gv r v
    occurrenceBefore s.t_v Γ_h = true ∧ head_covers gv.T B s.C_v = true ∧
      occurrenceAtLeast s.e_v Γ_e = true))

/-- `favorable_support(Σ, r, Γ, B) = w({v ∈ V: t_v < Γ, B ⪯ C_v} ∪ {v ∈ V: e_v < Γ})`. -/
def favorable_support (E : Env V) (gv : GradeView V) (r : Round) (Γ : Time)
    (B : Block V) : Nat :=
  E.electorate.weightOf (Finset.univ.filter (fun v =>
    let s := summary gv r v
    (occurrenceBefore s.t_v Γ = true ∧ head_covers gv.T B s.C_v = true) ∨
      occurrenceBefore s.e_v Γ = true))

/-- `G2(B) ⟺ direct_support(Σ, r, Γ_r^{−1}, Γ_r^2, B) ≥ m`. -/
def G2 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  decide (E.m ≤ direct_support E gv r (hc.Γ_neg1 E.Δ r) (hc.Γ_2 E.Δ r) B)

/-- `G1(B) ⟺ direct_support(Σ, r, Γ_r^0, Γ_r^0, B) ≥ m`. -/
def G1 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  decide (E.m ≤ direct_support E gv r (hc.Γ_0 E.Δ r) (hc.Γ_0 E.Δ r) B)

/-- `G0(B) ⟺ favorable_support(Σ, r, Γ_r^1, B) ≥ m`. -/
def G0 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  decide (E.m ≤ favorable_support E gv r (hc.Γ_1 E.Δ r) B)


/-- `g0_clear(Σ, r, B)`: no processed block stamped before `Γ_r^1` conflicts with `B` and holds
    grade 0. -/
def g0_clear (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  let freeze := hc.Γ_1 E.Δ r
  let vetoes := gv.T.filter (fun B' =>
    stampedBefore gv.timestamp_block freeze B' = true ∧
      Block.conflicts B' B = true ∧
      G0 E gv hc r B' = true)
  decide (vetoes.card = 0)

/-! ## The fresh SG root -/

/-- The fresh SG root: the deepest block of the filtered tree with grade 1. -/
def fresh_anchor (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Option (Block V) :=
  Block.deepest? ((Protocol.get_filtered_block_tree st.toFG).filter
    (fun B => G1 E st.gradeView hc r B = true))


/-- The round's stable-record root: the deepest G2 block of the filtered tree, or the FG root when
    there is none. -/
def current_stable_root (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (r : Round) : Option (Block V) :=
  some (match Block.deepest? ((Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => G2 E st.gradeView hc r B = true)) with
    | some G => G
    | none => Protocol.get_fg_root st.toFG)

/-- The absolute-grade read of round `r`. -/
def currentGradeRead (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (r : Round) : GradeRead V where
  anchor :=
    match fresh_anchor E hc st r with
    | some A => A
    | none =>
      let root := Protocol.get_fg_root st.toFG
      let tree := Protocol.get_filtered_block_tree st.toFG
      if (st.T.filter (fun B => G1 E st.gradeView hc r B = true)).Nonempty then root
      else Protocol.majority_fork_choice E st.sg_votes hc.η_SG st.T root tree r
  Q2 := Block.deepest? ((Protocol.get_filtered_block_tree st.toFG).filter
    (fun B => G2 E st.gradeView hc r B = true))
  clear := fun B => g0_clear E st.gradeView hc r B
  rawG2 := (st.T.filter (fun B => G2 E st.gradeView hc r B = true)).Nonempty
  rawG2_decidable := inferInstance

/-- The absolute-grade reference contract. -/
def GradeContract.current : GradeContract V where
  read := currentGradeRead
  sgVote := currentSGVote
  confirmationSG := .optional (fun E hc st _ =>
    some (currentSGVote st (currentGradeRead E hc st (hc.round_of st.s))))
  stableRoot := current_stable_root

/-- `grade2_block_with` at the absolute-grade reference contract. -/
def grade2_block (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Option (Block V) :=
  grade2_block_with GradeContract.current E hc st r

/-- `fg_source_with` at the absolute-grade reference contract. -/
def fg_source (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) : Option (Block V) :=
  fg_source_with GradeContract.current E hc st r A_G2

/-- `get_sg_root(Σ, r)` at the absolute-grade reference contract: the fresh SG root when one exists,
    and the relative-majority root otherwise. -/
def get_sg_root (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Block V :=
  get_sg_root_with GradeContract.current E hc st r

end Protocol

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

end Protocol

namespace Internal

open Protocol (HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store with its time set to `t` and its slot to the slot of `t`. -/
def tick_store (E : Env V) (st : Protocol.Store V) (t : Time) : Protocol.Store V :=
  { st with t := t, s := E.slotOf t }

end Internal
end DecoupledConsensusModel

end
