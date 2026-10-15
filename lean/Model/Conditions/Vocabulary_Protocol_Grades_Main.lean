import Proofs.Vocabulary.Protocol.Grades.Main
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing

/-!
# Confirmation evaluation

The vote sets, count, score, eligibility test, tree, root, anchor and walk of a slot's confirmation
evaluation, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- For each outcome `τ` of `st.tau`, the slot-`s` votes of `st`'s pool whose `τ` stamp is before
    the support cutoff of slot `s`. -/
def Vocabulary.Protocol.confEarly (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) :
    DC.NDRE (Finset (GoldfishVote V)) :=
  (fun τ => beforeCutoff τ (M.support_cutoff E s) (st.pool s)) <$> st.tau

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The slot-`s` votes of `st`'s pool received before slot `s`'s confirmation time. -/
def Vocabulary.Protocol.confLate (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (M.confirmation_time E s) (st.pool s)

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- For each outcome `e` of `confEarly`, the votes of `e` with no second vote in `confLate`. -/
def Vocabulary.Protocol.confVotes (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) :
    DC.NDRE (Finset (GoldfishVote V)) :=
  (fun e => e.filter
    (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true)) <$>
    Restated.Vocabulary.Protocol.confEarly M E st s

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The number of voters of `confLate` at slot `s`. -/
def Vocabulary.Protocol.confCount (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) : Nat :=
  M.voters_count E (Restated.Vocabulary.Protocol.confLate M E st s) s

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- For each outcome `u` of `confVotes`, the outcomes of the Goldfish score of `B` in `st`'s block
    tree with `u` in both vote arguments. -/
def Vocabulary.Protocol.confScore (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) (B : Block V) :
    DC.NDRE Nat := do
  let u ← Restated.Vocabulary.Protocol.confVotes M E st s
  M.goldfish_score E st.T u u s B

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The tests "`confCount` is less than twice `sc B`", for every outcome `u` of `confVotes` and
    every function `sc` giving every block `B` an outcome of its Goldfish score with `u` in both
    vote arguments. -/
def Vocabulary.Protocol.confEligible (M : Record.Model V) (E : Env V) (st : M.S) (s : Slot) :
    DC.NDRE (Block V → Bool) := do
  let u ← Restated.Vocabulary.Protocol.confVotes M E st s
  let sc ← (ExceptT.lift {sc : Block V → Nat | ∀ B, M.goldfish_score E st.T u u s B ⇢ sc B} :
    DC.NDRE (Block V → Nat))
  pure (fun B => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B))

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The filtered block tree of `st`, which the confirmation walk descends. -/
def Vocabulary.Protocol.confTree (M : Record.Model V) (st : M.S) : Finset (Block V) :=
  M.get_filtered_block_tree st.toHealing.toFG

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The FG root of `st`. -/
def Vocabulary.Protocol.confRoot (M : Record.Model V) (st : M.S) : Block V :=
  M.get_fg_root st.toHealing.toFG

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The outcomes of the SG root of the round of `st`'s slot under `contract`. -/
def Vocabulary.Protocol.confAnchorWith (M : Record.Model V) (contract : M.Contract) (E : Env V) (hc : HealConfig)
    (st : M.S) : DC.NDRE (Block V) :=
  M.get_sg_root_with contract E hc st.toHealing (M.round_of hc st.s)

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- The outcomes of the GHOST walk from an outcome of `confAnchorWith` in `confTree`, with a score
    function `sc` built from one outcome of `confVotes` and the eligibility test "`confCount` is
    less than twice `sc B`". -/
def Vocabulary.Protocol.confWalkWith (M : Record.Model V) (contract : M.Contract) (E : Env V) (hc : HealConfig)
    (st : M.S) (s : Slot) : DC.NDRE (Block V) := do
  let A ← Restated.Vocabulary.Protocol.confAnchorWith M contract E hc st
  let u ← Restated.Vocabulary.Protocol.confVotes M E st s
  let sc ← (ExceptT.lift {sc : Block V → Nat | ∀ B, M.goldfish_score E st.T u u s B ⇢ sc B} :
    DC.NDRE (Block V → Nat))
  M.ghost A (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B))

end

section
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.confEarly` has the single
    outcome `DecoupledConsensusModel.Protocol.confEarly`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confEarly_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Restated.Vocabulary.Protocol.confEarly (V := V) Record.Model.vocabulary E st s =
      pure (_root_.DecoupledConsensusModel.Protocol.confEarly (V := V) E st s) :=
  map_pure _ _

/-- `DecoupledConsensusModel.Protocol.confLate` equals `Restated.Vocabulary.Protocol.confLate` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confLate_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    _root_.DecoupledConsensusModel.Protocol.confLate (V := V) E st s = Restated.Vocabulary.Protocol.confLate (V := V) Record.Model.vocabulary E st s :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.confVotes` has the single
    outcome `DecoupledConsensusModel.Protocol.confVotes`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confVotes_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Restated.Vocabulary.Protocol.confVotes (V := V) Record.Model.vocabulary E st s =
      pure (_root_.DecoupledConsensusModel.Protocol.confVotes (V := V) E st s) := by
  rw [Restated.Vocabulary.Protocol.confVotes, Vocabulary.Protocol.confEarly_vocabulary_eq, map_pure]
  rfl

/-- `DecoupledConsensusModel.Protocol.confCount` equals `Restated.Vocabulary.Protocol.confCount` at
    the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confCount_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    _root_.DecoupledConsensusModel.Protocol.confCount (V := V) E st s = Restated.Vocabulary.Protocol.confCount (V := V) Record.Model.vocabulary E st s :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.confScore` has the single
    outcome `DecoupledConsensusModel.Protocol.confScore`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confScore_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) (B : Block V) :
    Restated.Vocabulary.Protocol.confScore (V := V) Record.Model.vocabulary E st s B =
      pure (_root_.DecoupledConsensusModel.Protocol.confScore (V := V) E st s B) := by
  rw [Restated.Vocabulary.Protocol.confScore, Vocabulary.Protocol.confVotes_vocabulary_eq, pure_bind]
  rfl

/-- At the model `Record.Model.vocabulary`, the only function giving every block `B` an outcome of its
    Goldfish score, with `DecoupledConsensusModel.Protocol.confVotes` in both vote arguments, is
    `DecoupledConsensusModel.Protocol.confScore`. -/
theorem Vocabulary.Protocol.confScore_choice_vocabulary (E : Env V)
    (st : (Record.Model.vocabulary (V := V)).S) (s : Slot) :
    {sc : Block V → Nat | ∀ B, (Record.Model.vocabulary (V := V)).goldfish_score E st.T
        (_root_.DecoupledConsensusModel.Protocol.confVotes E st s)
        (_root_.DecoupledConsensusModel.Protocol.confVotes E st s) s B ⇢ sc B} =
      {_root_.DecoupledConsensusModel.Protocol.confScore (V := V) E st s} := by
  ext sc
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext B
    exact (Record.returns_pure _ _).1 (h B)
  · intro h B
    subst h
    exact (Record.returns_pure _ _).2 rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.confEligible` has the single
    outcome `DecoupledConsensusModel.Protocol.confEligible`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confEligible_vocabulary_eq (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Restated.Vocabulary.Protocol.confEligible (V := V) Record.Model.vocabulary E st s =
      pure (_root_.DecoupledConsensusModel.Protocol.confEligible (V := V) E st s) := by
  rw [Restated.Vocabulary.Protocol.confEligible, Vocabulary.Protocol.confVotes_vocabulary_eq, pure_bind,
    Vocabulary.Protocol.confScore_choice_vocabulary, ← Set.pure_def, ExceptT.lift_pure, pure_bind]
  rfl

/-- `DecoupledConsensusModel.Protocol.confTree` equals `Restated.Vocabulary.Protocol.confTree` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confTree_vocabulary_eq (st : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.confTree (V := V) st = Restated.Vocabulary.Protocol.confTree (V := V) Record.Model.vocabulary st :=
  rfl

/-- `DecoupledConsensusModel.Protocol.confRoot` equals `Restated.Vocabulary.Protocol.confRoot` at the
    model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confRoot_vocabulary_eq (st : Protocol.Store V) :
    _root_.DecoupledConsensusModel.Protocol.confRoot (V := V) st = Restated.Vocabulary.Protocol.confRoot (V := V) Record.Model.vocabulary st :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.confAnchorWith` has the single
    outcome `DecoupledConsensusModel.Protocol.confAnchorWith`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confAnchorWith_vocabulary_eq (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig) (st : Protocol.Store V) :
    Restated.Vocabulary.Protocol.confAnchorWith (V := V) Record.Model.vocabulary contract E hc st =
      pure (_root_.DecoupledConsensusModel.Protocol.confAnchorWith (V := V) contract E hc st) :=
  rfl

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Protocol.confWalkWith` has the single
    outcome `DecoupledConsensusModel.Protocol.confWalkWith`. -/
@[record_vocabulary]
theorem Vocabulary.Protocol.confWalkWith_vocabulary_eq (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig) (st : Protocol.Store V) (s : Slot) :
    Restated.Vocabulary.Protocol.confWalkWith (V := V) Record.Model.vocabulary contract E hc st s =
      pure (_root_.DecoupledConsensusModel.Protocol.confWalkWith (V := V) contract E hc st s) := by
  rw [Restated.Vocabulary.Protocol.confWalkWith, Vocabulary.Protocol.confAnchorWith_vocabulary_eq,
    pure_bind, Vocabulary.Protocol.confVotes_vocabulary_eq, pure_bind,
    Vocabulary.Protocol.confScore_choice_vocabulary, ← Set.pure_def, ExceptT.lift_pure, pure_bind]
  rfl

end

end DecoupledConsensusModel.Sts.Restated
