import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Vocabulary.Protocol.Grades
import Model.Record.Wiring

/-!
# Grade vocabulary

Round batches, batch summaries, direct and favorable support, the grades `G2`, `G1` and `G0`, the
grade-0 clear test, the fresh anchor, the stable root, the grade read and the grade contract, over a
model `M : Record.Model V`, each read through a function giving an outcome of the head-covering
test.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

noncomputable section

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- Round `r`'s batch: the SG votes of round `r − 1` in `gv`, and empty for round 0. -/
def Vocabulary.Protocol.round_batch (M : Record.Model V) (gv : M.GV) (r : Round) : Finset (SGVote V) :=
  if r = 0 then ∅ else gv.sg_votes (r - 1)

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- The batch summary `(C_v, t_v, e_v)` of `v` in round `r`, read off `v`'s votes in the round
    batch. -/
def Vocabulary.Protocol.summary (M : Record.Model V) (gv : M.GV) (r : Round) (v : V) : BatchSummary :=
  let batch := Protocol.sg_votes_by (Restated.Vocabulary.Protocol.round_batch M gv r) v
  let τ := Protocol.sg_resolution_time gv.T gv.timestamp_block gv.timestamp_sg_vote
  let headed := batch_first? τ (batch.filter (fun u =>
    u.confirmed.isSome ∧ Protocol.sg_resolved gv.T u = true))
  { C_v := headed.bind SGVote.confirmed
    t_v := headed.elim none τ
    e_v := equivocation_instant gv.timestamp_sg_vote batch }

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- `cov B k` is an outcome of the test `M.head_covers T B k`, for every block `B` and key `k`. -/
def Vocabulary.Protocol.HeadCoversOutcomes (M : Record.Model V) (T : Finset (Block V))
    (cov : Block V → Option BlockId → Bool) : Prop :=
  ∀ (B : Block V) (k : Option BlockId), M.head_covers T B k ⇢ cov B k

/-- The weight of the validators `v` whose summary in round `r` has resolution time before `Γ_h`, a
    head covering `B` by `cov`, and equivocation time at least `Γ_e`. -/
def Vocabulary.Protocol.direct_support_withCovers (M : Record.Model V) (E : Env V) (gv : M.GV)
    (r : Round) (Γ_h Γ_e : Time) (B : Block V) (cov : Block V → Option BlockId → Bool) : Nat :=
  E.electorate.weightOf (Finset.univ.filter (fun v =>
    let s := Restated.Vocabulary.Protocol.summary M gv r v
    occurrenceBefore s.t_v Γ_h = true ∧ cov B s.C_v = true ∧
      occurrenceAtLeast s.e_v Γ_e = true))

/-- The set of the weights `direct_support_withCovers … cov`, for every function `cov` giving every
    block and key an outcome of `M.head_covers` on `gv`'s tree. -/
def Vocabulary.Protocol.direct_support (M : Record.Model V) (E : Env V) (gv : M.GV) (r : Round) (Γ_h Γ_e : Time)
    (B : Block V) : DC.NDR Nat :=
  {w | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M gv.T cov ∧
    w = Restated.Vocabulary.Protocol.direct_support_withCovers M E gv r Γ_h Γ_e B cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- The weight of the validators `v` whose summary in round `r` has resolution time before `Γ` and a
    head covering `B` by `cov`, or equivocation time before `Γ`. -/
def Vocabulary.Protocol.favorable_support_withCovers (M : Record.Model V) (E : Env V) (gv : M.GV)
    (r : Round) (Γ : Time) (B : Block V) (cov : Block V → Option BlockId → Bool) : Nat :=
  E.electorate.weightOf (Finset.univ.filter (fun v =>
    let s := Restated.Vocabulary.Protocol.summary M gv r v
    (occurrenceBefore s.t_v Γ = true ∧ cov B s.C_v = true) ∨
      occurrenceBefore s.e_v Γ = true))

/-- The set of the weights `favorable_support_withCovers … cov`, for every function `cov` giving
    every block and key an outcome of `M.head_covers` on `gv`'s tree. -/
def Vocabulary.Protocol.favorable_support (M : Record.Model V) (E : Env V) (gv : M.GV) (r : Round) (Γ : Time)
    (B : Block V) : DC.NDR Nat :=
  {w | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M gv.T cov ∧
    w = Restated.Vocabulary.Protocol.favorable_support_withCovers M E gv r Γ B cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- Whether `m ≤ direct_support_withCovers` at the cutoffs `Γ_r^{−1}` and `Γ_r^2`, with `cov`. -/
def Vocabulary.Protocol.G2_withCovers (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig)
    (r : Round) (B : Block V) (cov : Block V → Option BlockId → Bool) : Bool :=
  decide (E.m ≤ Restated.Vocabulary.Protocol.direct_support_withCovers M E gv r
    (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc E.Δ r)
    (Restated.Vocabulary.Protocol.HealConfig.Γ_2 M hc E.Δ r) B cov)

/-- The set of the values `G2_withCovers … cov`, for every function `cov` giving every block and key
    an outcome of `M.head_covers` on `gv`'s tree. -/
def Vocabulary.Protocol.G2 (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig) (r : Round)
    (B : Block V) : DC.NDR Bool :=
  {g | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M gv.T cov ∧
    g = Restated.Vocabulary.Protocol.G2_withCovers M E gv hc r B cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- Whether `m ≤ direct_support_withCovers` at the cutoffs `Γ_r^0` and `Γ_r^0`, with `cov`. -/
def Vocabulary.Protocol.G1_withCovers (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig)
    (r : Round) (B : Block V) (cov : Block V → Option BlockId → Bool) : Bool :=
  decide (E.m ≤ Restated.Vocabulary.Protocol.direct_support_withCovers M E gv r
    (Restated.Vocabulary.Protocol.HealConfig.Γ_0 M hc E.Δ r)
    (Restated.Vocabulary.Protocol.HealConfig.Γ_0 M hc E.Δ r) B cov)

/-- The set of the values `G1_withCovers … cov`, for every function `cov` giving every block and key
    an outcome of `M.head_covers` on `gv`'s tree. -/
def Vocabulary.Protocol.G1 (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig) (r : Round)
    (B : Block V) : DC.NDR Bool :=
  {g | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M gv.T cov ∧
    g = Restated.Vocabulary.Protocol.G1_withCovers M E gv hc r B cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- Whether `m ≤ favorable_support_withCovers` at the cutoff `Γ_r^1`, with `cov`. -/
def Vocabulary.Protocol.G0_withCovers (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig)
    (r : Round) (B : Block V) (cov : Block V → Option BlockId → Bool) : Bool :=
  decide (E.m ≤ Restated.Vocabulary.Protocol.favorable_support_withCovers M E gv r
    (Restated.Vocabulary.Protocol.HealConfig.Γ_1 M hc E.Δ r) B cov)

/-- The set of the values `G0_withCovers … cov`, for every function `cov` giving every block and key
    an outcome of `M.head_covers` on `gv`'s tree. -/
def Vocabulary.Protocol.G0 (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig) (r : Round)
    (B : Block V) : DC.NDR Bool :=
  {g | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M gv.T cov ∧
    g = Restated.Vocabulary.Protocol.G0_withCovers M E gv hc r B cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- Whether no block of `gv`'s tree stamped before the freeze `Γ_r^1` conflicts with `B` and has
    `G0_withCovers … cov` true. -/
def Vocabulary.Protocol.g0_clear_withCovers (M : Record.Model V) (E : Env V) (gv : M.GV)
    (hc : HealConfig) (r : Round) (B : Block V) (cov : Block V → Option BlockId → Bool) : Bool :=
  let freeze := Restated.Vocabulary.Protocol.HealConfig.Γ_1 M hc E.Δ r
  let vetoes := gv.T.filter (fun B' =>
    stampedBefore gv.timestamp_block freeze B' = true ∧
      Block.conflicts B' B = true ∧
      Restated.Vocabulary.Protocol.G0_withCovers M E gv hc r B' cov = true)
  decide (vetoes.card = 0)

/-- The set of the values `g0_clear_withCovers … cov`, for every function `cov` giving every block
    and key an outcome of `M.head_covers` on `gv`'s tree. -/
def Vocabulary.Protocol.g0_clear (M : Record.Model V) (E : Env V) (gv : M.GV) (hc : HealConfig) (r : Round)
    (B : Block V) : DC.NDR Bool :=
  {g | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M gv.T cov ∧
    g = Restated.Vocabulary.Protocol.g0_clear_withCovers M E gv hc r B cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- The deepest block of `st`'s filtered tree with `G1_withCovers … cov` true, if any. -/
def Vocabulary.Protocol.fresh_anchor_withCovers (M : Record.Model V) (E : Env V) (hc : HealConfig)
    (st : M.HS) (r : Round) (cov : Block V → Option BlockId → Bool) : Option (Block V) :=
  Block.deepest? ((M.get_filtered_block_tree st.toFG).filter
    (fun B => Restated.Vocabulary.Protocol.G1_withCovers M E (M.gradeView st) hc r B cov = true))

/-- The set of the values `fresh_anchor_withCovers … cov`, for every function `cov` giving every
    block and key an outcome of `M.head_covers` on the tree of `st`'s grade view. -/
def Vocabulary.Protocol.fresh_anchor (M : Record.Model V) (E : Env V) (hc : HealConfig) (st : M.HS) (r : Round) :
    DC.NDR (Option (Block V)) :=
  {a | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M (M.gradeView st).T cov ∧
    a = Restated.Vocabulary.Protocol.fresh_anchor_withCovers M E hc st r cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- The deepest block of `st`'s filtered tree with `G2_withCovers … cov` true, or the FG root of
    `st` when there is none. -/
def Vocabulary.Protocol.current_stable_root_withCovers (M : Record.Model V) (E : Env V)
    (hc : HealConfig) (st : M.HS) (r : Round) (cov : Block V → Option BlockId → Bool) :
    Option (Block V) :=
  some (match Block.deepest? ((M.get_filtered_block_tree st.toFG).filter
      (fun B => Restated.Vocabulary.Protocol.G2_withCovers M E (M.gradeView st) hc r B cov = true)) with
    | some G => G
    | none => M.get_fg_root st.toFG)

/-- The set of the values `current_stable_root_withCovers … cov`, for every function `cov` giving
    every block and key an outcome of `M.head_covers` on the tree of `st`'s grade view. -/
def Vocabulary.Protocol.current_stable_root (M : Record.Model V) (E : Env V) (hc : HealConfig) (st : M.HS)
    (r : Round) : DC.NDR (Option (Block V)) :=
  {a | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M (M.gradeView st).T cov ∧
    a = Restated.Vocabulary.Protocol.current_stable_root_withCovers M E hc st r cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- When `fresh_anchor_withCovers … cov` is `some A`, the block `A`; otherwise, when some block of
    `st`'s tree has `G1_withCovers … cov` true, the FG root of `st`; otherwise every block the
    relative-majority walk from the FG root over `st`'s filtered tree can return. -/
def Vocabulary.Protocol.currentAnchor_withCovers (M : Record.Model V) (E : Env V) (hc : HealConfig)
    (st : M.HS) (r : Round) (cov : Block V → Option BlockId → Bool) : DC.NDR (Block V) :=
  match Restated.Vocabulary.Protocol.fresh_anchor_withCovers M E hc st r cov with
  | some A => {A}
  | none =>
    let root := M.get_fg_root st.toFG
    let tree := M.get_filtered_block_tree st.toFG
    if (st.T.filter (fun B =>
        Restated.Vocabulary.Protocol.G1_withCovers M E (M.gradeView st) hc r B cov = true)).Nonempty
    then {root}
    else {a | Restated.Vocabulary.Protocol.majority_fork_choice M E st.sg_votes hc.η_SG st.T root
      tree r ⇢ a}

/-- The grade reads whose anchor is one `currentAnchor_withCovers … cov` gives, whose `Q2` is the
    deepest block of `st`'s filtered tree with `G2_withCovers … cov` true, whose clear test is
    `g0_clear_withCovers … cov`, and whose raw grade-2 test says some block of `st`'s tree has
    `G2_withCovers … cov` true. -/
def Vocabulary.Protocol.currentGradeRead_withCovers (M : Record.Model V) (E : Env V)
    (hc : HealConfig) (st : M.HS) (r : Round) (cov : Block V → Option BlockId → Bool) :
    DC.NDR (GradeRead V) :=
  (fun a : Block V =>
    ({ anchor := a
       Q2 := Block.deepest? ((M.get_filtered_block_tree st.toFG).filter
         (fun B => Restated.Vocabulary.Protocol.G2_withCovers M E (M.gradeView st) hc r B cov = true))
       clear := fun B => Restated.Vocabulary.Protocol.g0_clear_withCovers M E (M.gradeView st) hc r B cov
       rawG2 := (st.T.filter (fun B =>
         Restated.Vocabulary.Protocol.G2_withCovers M E (M.gradeView st) hc r B cov = true)).Nonempty
       rawG2_decidable := inferInstance } : GradeRead V)) ''
    Restated.Vocabulary.Protocol.currentAnchor_withCovers M E hc st r cov

/-- The set of the grade reads `currentGradeRead_withCovers … cov` gives, for every function `cov`
    giving every block and key an outcome of `M.head_covers` on the tree of `st`'s grade view. -/
def Vocabulary.Protocol.currentGradeRead (M : Record.Model V) (E : Env V) (hc : HealConfig) (st : M.HS)
    (r : Round) : DC.NDR (GradeRead V) :=
  {g | ∃ cov, Restated.Vocabulary.Protocol.HeadCoversOutcomes M (M.gradeView st).T cov ∧
    g ∈ Restated.Vocabulary.Protocol.currentGradeRead_withCovers M E hc st r cov}

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- The set of contracts built with `M.mkContract` that read grades by a choice of grade reads from
    `currentGradeRead_withCovers`, compute their SG vote by `M.currentSGVote`, select as their SG
    candidate the SG vote of that grade read at the round of the store's slot, and read their stable
    root by `current_stable_root_withCovers`. -/
def Vocabulary.Protocol.GradeContract.current (M : Record.Model V) : DC.NDR M.Contract :=
  {c | ∃ (cov : M.HS → Block V → Option BlockId → Bool)
      (rd : Env V → HealConfig → M.HS → Round → GradeRead V),
    (∀ st, Restated.Vocabulary.Protocol.HeadCoversOutcomes M (M.gradeView st).T (cov st)) ∧
    (∀ E hc st r, rd E hc st r ∈
      Restated.Vocabulary.Protocol.currentGradeRead_withCovers M E hc st r (cov st)) ∧
    c = M.mkContract rd M.currentSGVote
      (fun E hc st _ => some (M.currentSGVote st (rd E hc st (M.round_of hc st.s))))
      (fun E hc st r => Restated.Vocabulary.Protocol.current_stable_root_withCovers M E hc st r (cov st))}

/-- The outcomes of `M.grade2_block_with` under every contract `GradeContract.current` gives. -/
def Vocabulary.Protocol.grade2_block (M : Record.Model V) (E : Env V) (hc : HealConfig) (st : M.HS) (r : Round) :
    DC.NDRE (Option (Block V)) := do
  let c ← (ExceptT.lift (Restated.Vocabulary.Protocol.GradeContract.current M) : DC.NDRE M.Contract)
  M.grade2_block_with c E hc st r

/-- The outcomes of `M.fg_source_with` under every contract `GradeContract.current` gives. -/
def Vocabulary.Protocol.fg_source (M : Record.Model V) (E : Env V) (hc : HealConfig) (st : M.HS) (r : Round)
    (A_G2 : Option (Block V)) : DC.NDRE (Option (Block V)) := do
  let c ← (ExceptT.lift (Restated.Vocabulary.Protocol.GradeContract.current M) : DC.NDRE M.Contract)
  M.fg_source_with c E hc st r A_G2

end

section
open DecoupledConsensusModel.Protocol
open Protocol (SGVote)

/-- `DecoupledConsensusModel.Protocol.round_batch` equals `Restated.Vocabulary.Protocol.round_batch`
    at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.round_batch_vocabulary_eq (gv : GradeView V) (r : Round) :
    _root_.DecoupledConsensusModel.Protocol.round_batch (V := V) gv r = Restated.Vocabulary.Protocol.round_batch (V := V) Record.Model.vocabulary gv r :=
  rfl

/-- `DecoupledConsensusModel.Protocol.summary` equals `Restated.Vocabulary.Protocol.summary` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.summary_vocabulary_eq (gv : GradeView V) (r : Round) (v : V) :
    _root_.DecoupledConsensusModel.Protocol.summary (V := V) gv r v = Restated.Vocabulary.Protocol.summary (V := V) Record.Model.vocabulary gv r v :=
  rfl

/-- At the model `Record.Model.vocabulary`, `cov` gives every block and key an outcome of
    `head_covers` on `T` exactly when `cov` is `DecoupledConsensusModel.Protocol.head_covers T`. -/
theorem Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff (T : Finset (Block V))
    (cov : Block V → Option BlockId → Bool) :
    Restated.Vocabulary.Protocol.HeadCoversOutcomes (V := V) Record.Model.vocabulary T cov ↔
      cov = fun B k => _root_.DecoupledConsensusModel.Protocol.head_covers T B k := by
  constructor
  · intro h
    funext B k
    exact (Record.returns_pure _ _).1 (h B k)
  · intro h B k
    subst h
    exact (Record.returns_pure _ _).2 rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.direct_support` is the
    singleton of `DecoupledConsensusModel.Protocol.direct_support`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.direct_support_vocabulary_eq (E : Env V) (gv : GradeView V) (r : Round) (Γ_h Γ_e : Time) (B : Block V) :
    Restated.Vocabulary.Protocol.direct_support (V := V) Record.Model.vocabulary E gv r Γ_h Γ_e B =
      {_root_.DecoupledConsensusModel.Protocol.direct_support (V := V) E gv r Γ_h Γ_e B} := by
  ext w
  simp only [Restated.Vocabulary.Protocol.direct_support, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.favorable_support` is the
    singleton of `DecoupledConsensusModel.Protocol.favorable_support`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.favorable_support_vocabulary_eq (E : Env V) (gv : GradeView V) (r : Round) (Γ : Time) (B : Block V) :
    Restated.Vocabulary.Protocol.favorable_support (V := V) Record.Model.vocabulary E gv r Γ B =
      {_root_.DecoupledConsensusModel.Protocol.favorable_support (V := V) E gv r Γ B} := by
  ext w
  simp only [Restated.Vocabulary.Protocol.favorable_support, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.G2` is the singleton of
    `DecoupledConsensusModel.Protocol.G2`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.G2_vocabulary_eq (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round) (B : Block V) :
    Restated.Vocabulary.Protocol.G2 (V := V) Record.Model.vocabulary E gv hc r B =
      {_root_.DecoupledConsensusModel.Protocol.G2 (V := V) E gv hc r B} := by
  ext g
  simp only [Restated.Vocabulary.Protocol.G2, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.G1` is the singleton of
    `DecoupledConsensusModel.Protocol.G1`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.G1_vocabulary_eq (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round) (B : Block V) :
    Restated.Vocabulary.Protocol.G1 (V := V) Record.Model.vocabulary E gv hc r B =
      {_root_.DecoupledConsensusModel.Protocol.G1 (V := V) E gv hc r B} := by
  ext g
  simp only [Restated.Vocabulary.Protocol.G1, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.G0` is the singleton of
    `DecoupledConsensusModel.Protocol.G0`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.G0_vocabulary_eq (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round) (B : Block V) :
    Restated.Vocabulary.Protocol.G0 (V := V) Record.Model.vocabulary E gv hc r B =
      {_root_.DecoupledConsensusModel.Protocol.G0 (V := V) E gv hc r B} := by
  ext g
  simp only [Restated.Vocabulary.Protocol.G0, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.g0_clear` is the singleton of
    `DecoupledConsensusModel.Protocol.g0_clear`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.g0_clear_vocabulary_eq (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round) (B : Block V) :
    Restated.Vocabulary.Protocol.g0_clear (V := V) Record.Model.vocabulary E gv hc r B =
      {_root_.DecoupledConsensusModel.Protocol.g0_clear (V := V) E gv hc r B} := by
  ext g
  simp only [Restated.Vocabulary.Protocol.g0_clear, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.fresh_anchor` is the singleton
    of `DecoupledConsensusModel.Protocol.fresh_anchor`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.fresh_anchor_vocabulary_eq (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Restated.Vocabulary.Protocol.fresh_anchor (V := V) Record.Model.vocabulary E hc st r =
      {_root_.DecoupledConsensusModel.Protocol.fresh_anchor (V := V) E hc st r} := by
  ext a
  simp only [Restated.Vocabulary.Protocol.fresh_anchor, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.current_stable_root` is the
    singleton of `DecoupledConsensusModel.Protocol.current_stable_root`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.current_stable_root_vocabulary_eq (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Restated.Vocabulary.Protocol.current_stable_root (V := V) Record.Model.vocabulary E hc st r =
      {_root_.DecoupledConsensusModel.Protocol.current_stable_root (V := V) E hc st r} := by
  ext a
  simp only [Restated.Vocabulary.Protocol.current_stable_root, Set.mem_setOf_eq, Set.mem_singleton_iff,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  rfl

/-- At the model `Record.Model.vocabulary`, `currentGradeRead_withCovers` with
    `DecoupledConsensusModel.Protocol.head_covers` on the tree of `st`'s grade view is the singleton
    of `DecoupledConsensusModel.Protocol.currentGradeRead`. -/
theorem Vocabulary.Protocol.currentGradeRead_withCovers_vocabulary_eq (E : Env V) (hc : HealConfig)
    (st : HealingStore V) (r : Round) :
    Restated.Vocabulary.Protocol.currentGradeRead_withCovers (V := V) Record.Model.vocabulary E hc st r
        (fun B k => _root_.DecoupledConsensusModel.Protocol.head_covers st.gradeView.T B k) =
      {_root_.DecoupledConsensusModel.Protocol.currentGradeRead (V := V) E hc st r} := by
  have hA : Restated.Vocabulary.Protocol.currentAnchor_withCovers (V := V) Record.Model.vocabulary E hc
      st r (fun B k => _root_.DecoupledConsensusModel.Protocol.head_covers st.gradeView.T B k) =
      {(_root_.DecoupledConsensusModel.Protocol.currentGradeRead (V := V) E hc st r).anchor} := by
    unfold Restated.Vocabulary.Protocol.currentAnchor_withCovers
    show (match _root_.DecoupledConsensusModel.Protocol.fresh_anchor (V := V) E hc st r with
      | some A => ({A} : Set (Block V))
      | none => _) = _
    unfold _root_.DecoupledConsensusModel.Protocol.currentGradeRead
    dsimp only
    cases _root_.DecoupledConsensusModel.Protocol.fresh_anchor (V := V) E hc st r with
    | some A => rfl
    | none =>
      dsimp only
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd h1 h2
      · exact absurd h2 h1
      · ext a
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
        rw [Vocabulary.Protocol.majority_fork_choice_vocabulary_eq]
        exact Record.returns_pure _ _
  unfold Restated.Vocabulary.Protocol.currentGradeRead_withCovers
  rw [hA, Set.image_singleton]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.currentGradeRead` is the
    singleton of `DecoupledConsensusModel.Protocol.currentGradeRead`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.currentGradeRead_vocabulary_eq (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Restated.Vocabulary.Protocol.currentGradeRead (V := V) Record.Model.vocabulary E hc st r =
      {_root_.DecoupledConsensusModel.Protocol.currentGradeRead (V := V) E hc st r} := by
  ext g
  simp only [Restated.Vocabulary.Protocol.currentGradeRead, Set.mem_setOf_eq,
    Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff, exists_eq_left]
  exact Set.ext_iff.1 (Vocabulary.Protocol.currentGradeRead_withCovers_vocabulary_eq E hc st r) g

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.GradeContract.current` is the
    singleton of `DecoupledConsensusModel.Protocol.GradeContract.current`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.GradeContract.current_vocabulary_eq :
    Restated.Vocabulary.Protocol.GradeContract.current (V := V) Record.Model.vocabulary =
      {_root_.DecoupledConsensusModel.Protocol.GradeContract.current (V := V)} := by
  ext c
  simp only [Restated.Vocabulary.Protocol.GradeContract.current, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨cov, rd, hcov, hrd, rfl⟩
    have hcov' : cov = fun st B k => _root_.DecoupledConsensusModel.Protocol.head_covers
        st.gradeView.T B k :=
      funext fun st => (Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff _ _).1 (hcov st)
    subst hcov'
    have hrd' : rd = _root_.DecoupledConsensusModel.Protocol.currentGradeRead (V := V) := by
      funext E hc st r
      exact Set.mem_singleton_iff.1
        ((Set.ext_iff.1 (Vocabulary.Protocol.currentGradeRead_withCovers_vocabulary_eq E hc st r) _).1
          (hrd E hc st r))
    subst hrd'
    rfl
  · intro h
    subst h
    refine ⟨fun st B k => _root_.DecoupledConsensusModel.Protocol.head_covers st.gradeView.T B k,
      _root_.DecoupledConsensusModel.Protocol.currentGradeRead (V := V),
      fun st => (Vocabulary.Protocol.HeadCoversOutcomes_vocabulary_iff _ _).2 rfl, ?_, rfl⟩
    intro E hc st r
    exact (Set.ext_iff.1 (Vocabulary.Protocol.currentGradeRead_withCovers_vocabulary_eq E hc st r) _).2
      (Set.mem_singleton _)

/-- At the model `Record.Model.vocabulary`, `GradeContract.current` is `pure` of
    `DecoupledConsensusModel.Protocol.GradeContract.current`, at the record's type of contracts. -/
theorem Vocabulary.Protocol.GradeContract.current_vocabulary_pure :
    Restated.Vocabulary.Protocol.GradeContract.current (V := V) Record.Model.vocabulary =
      (pure (_root_.DecoupledConsensusModel.Protocol.GradeContract.current (V := V)) :
        Set (Record.Model.vocabulary (V := V)).Contract) := by
  rw [Vocabulary.Protocol.GradeContract.current_vocabulary_eq]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.grade2_block` has the single
    outcome `DecoupledConsensusModel.Protocol.grade2_block`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.grade2_block_vocabulary_eq (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Restated.Vocabulary.Protocol.grade2_block (V := V) Record.Model.vocabulary E hc st r =
      pure (_root_.DecoupledConsensusModel.Protocol.grade2_block (V := V) E hc st r) := by
  rw [Restated.Vocabulary.Protocol.grade2_block, Vocabulary.Protocol.GradeContract.current_vocabulary_pure,
    ExceptT.lift_pure, pure_bind]
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.fg_source` has the single
    outcome `DecoupledConsensusModel.Protocol.fg_source`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.fg_source_vocabulary_eq (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) :
    Restated.Vocabulary.Protocol.fg_source (V := V) Record.Model.vocabulary E hc st r A_G2 =
      pure (_root_.DecoupledConsensusModel.Protocol.fg_source (V := V) E hc st r A_G2) := by
  rw [Restated.Vocabulary.Protocol.fg_source, Vocabulary.Protocol.GradeContract.current_vocabulary_pure,
    ExceptT.lift_pure, pure_bind]
  rfl

end

end

end DecoupledConsensusModel.Sts.Restated
