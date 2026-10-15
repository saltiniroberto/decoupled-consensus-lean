import Proofs.Instance.Equalities.Schedule
import Proofs.Instance.Equalities.Store
import Proofs.Instance.Equalities.ChainState
import Proofs.Instance.Equalities.ValidatorClient
import Proofs.Instance.Equalities.ForkChoice
import Proofs.Instance.Equalities.Grades
import Proofs.Instance.Equalities.Handlers
import Proofs.Instance.Equalities.Duties
import Proofs.Instance.Equalities.Images
import Proofs.Instance.Wiring
import Model.Record.Model

/-!
# Shared definitions of the member pages

What the pages defining the members of `Model.specDraft` share: `successOutcomes`, the unread
configurations, the grade clipping tested on block images, the fill of pending grade results,
`orVocabulary`, and the spec's block admission split into its parts in the namespace
`SpecDraftRecord.Handlers`.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open Spec
open scoped DC

/-- `successOutcomes r`: the outcomes of the routine result `r`, the one outcome `.ok a` when `r` is
    the answer `a`, and none when `r` fails. -/
def successOutcomes {α : Type} (r : DC.DRE α) : DC.NDRE α :=
  ExceptT.mk (match r with
    | .ok a => ({Except.ok a} : Set (DC.DRE α))
    | .error _ => (∅ : Set (DC.DRE α)))

/-- The outcomes of `successOutcomes r` are exactly `.ok a` for the answer `a` of `r`. -/
theorem mem_successOutcomes_run {α : Type} (r : DC.DRE α) (x : DC.DRE α) :
    x ∈ (successOutcomes r).run ↔ ∃ a, r = .ok a ∧ x = .ok a := by
  cases r with
  | ok b =>
    simp only [successOutcomes, ExceptT.run_mk, Set.mem_singleton_iff, Except.ok.injEq]
    exact ⟨fun h => ⟨b, rfl, h⟩, fun ⟨a, ha, hx⟩ => by rw [hx, ha]⟩
  | error e =>
    simp only [successOutcomes, ExceptT.run_mk, Set.mem_empty_iff_false, false_iff]
    rintro ⟨a, ha, _⟩
    cases ha

/-- `successOutcomes r` can return `a` exactly when `r = .ok a`. -/
theorem returns_successOutcomes {α : Type} (r : DC.DRE α) (a : α) :
    DecoupledConsensusModel.Sts.Record.Returns (successOutcomes r) a ↔ r = .ok a := by
  unfold DecoupledConsensusModel.Sts.Record.Returns
  rw [mem_successOutcomes_run]
  constructor
  · rintro ⟨b, hb, hx⟩
    cases hx
    exact hb
  · intro h
    exact ⟨a, h, rfl⟩

/-- The round schedule given to `Config.toSpec` by members whose routine reads none: round length
    `R = 3` and lookback `η_SG = 1`. -/
def unreadHealConfig : DecoupledConsensusModel.Protocol.HealConfig where
  R := 3
  R_ge_three := le_refl 3
  η_SG := 1
  η_SG_ge_one := le_refl 1

/-- The height parameters given to `Config.toSpec` by members whose routine reads none: `K = 4`,
    `D = 2` and `timeoutDelay = 0`. -/
def unreadHeightConfig : DecoupledConsensusModel.Protocol.HeightConfig where
  K := 4
  D := 2
  timeoutDelay := 0
  K_ge_four := le_refl 4
  D_ge_two := le_refl 2

/-! ## The grade clipping, with the compatibility tested on the images -/

section ImageClip

open scoped Spec

variable {V : Type} [DecidableEq V]

/-- `clipBlockImage F g`: the deepest ancestor of `g`, `g` itself included, whose image is
    compatible with the block `F`. -/
def clipBlockImage (F : DecoupledConsensusModel.Block V) (g : Block V) : Block V := Id.run do
  let mut g := g
  for _ in [:g.depth + 1] do
    if DecoupledConsensusModel.Block.compatible g.toProof F then
      return g
    g ← g.parent
  return g

/-- `clipResultImage F result`: the grade result `result` with its block, if any, replaced by
    `clipBlockImage F` of it. -/
def clipResultImage (F : DecoupledConsensusModel.Block V) (result : GradeResult V) :
    GradeResult V :=
  Id.run do
  if result ≠ .pending then
    let G := result.block
    if G ≠ none then
      return .computed (clipBlockImage F G.value)
  return result

end ImageClip

/-! ## The fill: a pending grade result read as computed with no block -/

section Fill

variable {V : Type}

/-- `fillResult result`: `result` with `pending` read as `computed none`. -/
def fillResult : GradeResult V → GradeResult V
  | .pending => .computed none
  | .computed G => .computed G

/-- `fillRound grades`: the round's grades with each of their three results passed to `fillResult`. -/
def fillRound (grades : RoundGrades V) : RoundGrades V :=
  ⟨fillResult grades.g0, fillResult grades.g1, fillResult grades.g2⟩

/-- `fill c`: the saved grades `c` with both their rounds' grades passed to `fillRound`, the round
    `c.round` kept. -/
def fill (c : SavedGrades V) : SavedGrades V :=
  ⟨c.round, fillRound c.current, fillRound c.next⟩

/-- `RoundComputed grades`: none of the three results of the round's grades is `pending`. -/
def RoundComputed (grades : RoundGrades V) : Prop :=
  grades.g0 ≠ .pending ∧ grades.g1 ≠ .pending ∧ grades.g2 ≠ .pending

/-- A filled result is never `pending`. -/
theorem fillResult_ne_pending (result : GradeResult V) : fillResult result ≠ .pending := by
  cases result <;> simp [fillResult]

/-- `fillResult` keeps a result that is not `pending`. -/
theorem fillResult_of_ne_pending {result : GradeResult V} (h : result ≠ .pending) :
    fillResult result = result := by
  cases result with
  | pending => exact absurd rfl h
  | computed G => rfl

/-- Every result of `fillRound grades` is computed. -/
theorem roundComputed_fillRound (grades : RoundGrades V) : RoundComputed (fillRound grades) :=
  ⟨fillResult_ne_pending _, fillResult_ne_pending _, fillResult_ne_pending _⟩

/-- `fill` keeps the round of the saved grades. -/
@[simp] theorem fill_round (c : SavedGrades V) : (fill c).round = c.round := rfl

/-- For `r = c.round` or `r = c.round + 1`,
    `saved_round_grades (fill c) r = fillRound (saved_round_grades c r)`. -/
theorem saved_round_grades_fill (c : SavedGrades V) {r : Round}
    (hr : r = c.round ∨ r = c.round + 1) :
    Protocol.saved_round_grades (fill c) r = fillRound (Protocol.saved_round_grades c r) := by
  unfold Protocol.saved_round_grades
  rcases hr with h | h
  · simp [fill, h]
  · subst h
    simp [fill]

/-- For a round `r` other than `c.round` and `c.round + 1`,
    `saved_round_grades (fill c) r = pending_round_grades`. -/
theorem saved_round_grades_fill_of_ne (c : SavedGrades V) {r : Round} (h0 : r ≠ c.round)
    (h1 : r ≠ c.round + 1) :
    Protocol.saved_round_grades (fill c) r = Protocol.pending_round_grades := by
  unfold Protocol.saved_round_grades
  simp [fill, h0, h1]

/-! ### The saved grades brought to the round a member reads -/

/-- For every round `ρ`,
    `saved_round_grades (fill (advance_to_round c ρ)) ρ = fillRound (saved_round_grades c ρ)`. -/
theorem saved_round_grades_fill_advance (c : SavedGrades V) (ρ : Round) :
    Protocol.saved_round_grades (fill (Protocol.advance_to_round c ρ)) ρ
      = fillRound (Protocol.saved_round_grades c ρ) := by
  by_cases h0 : ρ = c.round
  · subst h0
    simp [Protocol.advance_to_round, Protocol.saved_round_grades, fill]
  · by_cases h1 : ρ = c.round + 1
    · subst h1
      simp [Protocol.advance_to_round, Protocol.saved_round_grades, fill]
    · simp [Protocol.advance_to_round, Protocol.saved_round_grades, fill, h0, h1]

/-- For every round `ρ`, no result of `saved_round_grades (fill (advance_to_round c ρ)) ρ` is
    `pending`. -/
theorem fill_advance_ne_pending (c : SavedGrades V) (ρ : Round) :
    RoundComputed (Protocol.saved_round_grades (fill (Protocol.advance_to_round c ρ)) ρ) := by
  rw [saved_round_grades_fill_advance]
  exact roundComputed_fillRound _

variable [DecidableEq V]

end Fill

/-! ## A fallback answer where a routine raises -/

/-- `orVocabulary r a`: the answer of `r` when it answers, and `a` when it raises. -/
def orVocabulary {α : Type} (r : DC.DRE α) (a : α) : DC.DRE α :=
  match r with
  | .ok b => .ok b
  | .error _ => .ok a

/-- `orVocabulary r a` always answers. -/
theorem orVocabulary_ok {α : Type} (r : DC.DRE α) (a : α) : ∃ b, orVocabulary r a = .ok b := by
  cases r with
  | ok x => exact ⟨x, rfl⟩
  | error e => exact ⟨a, rfl⟩

/-! ## The block admission, split into its parts -/

namespace Handlers

open Spec
open scoped Spec

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config) (P : Provisional V)

/-- `blockCore C P st B`: the first five steps of `Protocol.add_block`: `B`'s chain state computed
    by `Protocol.state_transition` from its parent's, `B` added to the tree and stamped at `st.t`,
    the Goldfish votes `B` includes admitted in order, and the finality fields updated from `B`'s
    chain state. The attestations `B` includes are not admitted. -/
def blockCore (st : Store V) (B : Block V) : Store V := Id.run do
  let mut st := st
  st.σ[B] ← Protocol.state_transition C P st.σ[B.parent] B
  st.T ← st.T ∪ {B}
  st.timestamp_block[B] ← st.t
  for vote in B.gf_votes do
    st ← Protocol.on_goldfish_vote_checked P st vote
  st ← Protocol.update_finality st B
  return st

/-- `admitBlockCore C P st B`: `blockCore C P st B` when the store admits `B`
    (`Protocol.block_admissible`), and `st` otherwise. -/
def admitBlockCore (st : Store V) (B : Block V) : Store V :=
  if Protocol.block_admissible C P st B then blockCore C P st B else st

/-- `Protocol.add_block` is `blockCore` followed by the admission of the attestations the block
    includes. -/
theorem add_block_eq (st : Store V) (B : Block V) :
    Protocol.add_block C P st B =
      Protocol.admit_attestations C (blockCore C P st B) B.attestations := rfl

/-- `Protocol.on_block C P st B` is
    `Protocol.admit_attestations C (admitBlockCore C P st B) B.attestations` when the store admits
    `B`, and `st` otherwise. -/
theorem on_block_eq (st : Store V) (B : Block V) :
    Protocol.on_block C P st B =
      if Protocol.block_admissible C P st B then
        Protocol.admit_attestations C (admitBlockCore C P st B) B.attestations
      else st := by
  unfold Protocol.on_block admitBlockCore
  by_cases h : Protocol.block_admissible C P st B = true
  · simp only [h, if_true, Id.run, add_block_eq]
    rfl
  · simp only [h]
    rfl

/-- `updateFinalityWith st σ`: the body of `Protocol.update_finality` with the chain state `σ`
    given. It raises `st.h_max` to `σ.h`; moves the justified block and height to `σ.J` and `σ.h_j`
    when `st.F` is an ancestor of `σ.J` and (`st.h_j`, root of `st.J`) is lexicographically smaller
    than (`σ.h_j`, root of `σ.J`); and moves the finalized block to `σ.F` when `st.F` is a strict
    ancestor of `σ.F`, `σ.F` is an ancestor of the justified block, and `σ.F` is in
    `Protocol.viable_tree`. -/
def updateFinalityWith (st : Store V) (σ : Protocol.ChainState V) : Store V := Id.run do
  let mut st := st
  st.h_max ← max st.h_max σ.h
  if st.F.ancestorEq σ.J && (st.h_j, st.J.root) <[lex] (σ.h_j, σ.J.root) then
    st.J ← σ.J
    st.h_j ← σ.h_j
  if st.F.ancestorStrict σ.F && σ.F.ancestorEq st.J &&
      σ.F ∈ Protocol.viable_tree st.σ st.F st.h_max st.T then
    st.F ← σ.F
  return st

omit [Fintype V] in
/-- `Protocol.update_finality st B = updateFinalityWith st (st.σ B)`. -/
theorem update_finality_eq (st : Store V) (B : Block V) :
    Protocol.update_finality st B = updateFinalityWith st (st.σ B) := rfl

/-- `onBlockUsing P st B buildState`: `st` unchanged when `B`'s slot is later than `st.s`, `B` is
    already in the tree, its parent is not, `st.F` is not an ancestor of `B`, `B`'s proposer is not
    its slot's, or its parent's slot is not earlier; otherwise the steps of `blockCore` with
    `buildState` in place of `Protocol.state_transition`. The attestations `B` includes are neither
    tested nor admitted. -/
def onBlockUsing (st : Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) : Store V := Id.run do
  let mut st := st
  if st.s < B.slot || B ∈ st.T || B.parent ∉ st.T then
    return st
  if ¬ st.F.ancestorEq B then
    return st
  if B.proposer? ≠ P.proposer B.slot then
    return st
  if ¬ (B.parent.slot < B.slot) then
    return st
  st.σ[B] ← buildState st.σ[B.parent]
  st.T ← st.T ∪ {B}
  st.timestamp_block[B] ← st.t
  for vote in B.gf_votes do
    st ← Protocol.on_goldfish_vote_checked P st vote
  st ← Protocol.update_finality st B
  return st

/-- `onBlockCheckedUsing C handle st B`: `handle st` when the attestations `B` includes pass
    `Protocol.included_attestations_admissible`, and `st` otherwise. -/
def onBlockCheckedUsing (handle : Store V → Store V) (st : Store V) (B : Block V) : Store V :=
  if Protocol.included_attestations_admissible C B then handle st else st

/-- `admitCarried C before after B`: `after` with the attestations `B` includes admitted when `B` is
    not in `before.T` and is in `after.T`, and `after` otherwise. -/
def admitCarried (before after : Store V) (B : Block V) : Store V :=
  if B ∉ before.T ∧ B ∈ after.T then Protocol.admit_attestations C after B.attestations
  else after

end Handlers

end SpecDraftRecord
