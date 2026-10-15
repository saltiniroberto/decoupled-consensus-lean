module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Confirmation
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk

@[expose] public section

/-!
# Confirmation at one store

The confirmation vote sets, count, score, eligibility, tree, root, anchor and walk of a store, and
the fact that under `HonestSupport` for `B` the slot-`s` confirmation records `B`.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The confirmation evaluation of a store -/

/-- `early`: the slot-`s` votes of the pool resolved before the support cutoff. -/
def confEarly (E : Env V) (st : Protocol.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)

/-- `late`: the slot-`s` votes of the pool stamped before the confirmation time. -/
def confLate (E : Env V) (st : Protocol.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)

/-- The numerator: the early votes whose validator has no second vote in the late set. -/
def confVotes (E : Env V) (st : Protocol.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  (confEarly E st s).filter
    (fun u => Protocol.no_second_vote_in (confLate E st s) u = true)

/-- The denominator: the number of participants of the late set. -/
def confCount (E : Env V) (st : Protocol.Store V) (s : Slot) : Nat :=
  Protocol.voters_count E (confLate E st s) s

/-- The score of `B`, with the numerator as both vote arguments. -/
def confScore (E : Env V) (st : Protocol.Store V) (s : Slot) (B : Block V) : Nat :=
  Protocol.goldfish_score E st.T (confVotes E st s) (confVotes E st s) s B

/-- The confirmation test: the count is less than twice the score. -/
def confEligible (E : Env V) (st : Protocol.Store V) (s : Slot) : Block V → Bool :=
  fun B => decide (confCount E st s < 2 * confScore E st s B)

/-- The tree the confirmation walk descends: the filtered block tree. -/
def confTree (st : Protocol.Store V) : Finset (Block V) :=
  Protocol.get_filtered_block_tree st.toHealing.toFG

/-- The FG root, which the confirmation records when the walk's result fails the confirmation test. -/
def confRoot (st : Protocol.Store V) : Block V :=
  Protocol.get_fg_root st.toHealing.toFG


/-- The confirmation anchor under `contract`: the SG root of the store's current round. -/
def confAnchorWith (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) : Block V :=
  Protocol.get_sg_root_with contract E hc st.toHealing (hc.round_of st.s)

/-- The confirmation walk under `contract`: `ghost` from the anchor over the confirmation tree, with
    the confirmation score and test. -/
def confWalkWith (contract : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) (s : Slot) : Block V :=
  Protocol.ghost (confAnchorWith contract E hc st) (confTree st) (confScore E st s)
    (confEligible E st s)


/-- `update_confirmation_with` records the walk's result when it passes the confirmation test, and
    the FG root otherwise. -/
theorem update_confirmation_with_live_confirmed (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.Store V) (s : Slot) :
    (Protocol.update_confirmation_with contract E hc st s).live_confirmed =
      if confEligible E st s (confWalkWith contract E hc st s) then
        confWalkWith contract E hc st s
      else confRoot st :=
  rfl


/-- The confirmation vote sets of a store have the `Numerator` shape. -/
theorem confNumerator (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Numerator (confEarly E st s) (confLate E st s) (confVotes E st s) where
  early_late := by
    intro u hu
    rw [confEarly, beforeCutoff, Finset.mem_filter] at hu
    refine beforeCutoff_mono _ (support_cutoff_le_confirmation_time E s) _ ?_
    rw [beforeCutoff, Finset.mem_filter]
    exact ⟨hu.1, Protocol.stampedBefore_of_resolution hu.2⟩
  filtered := rfl

theorem confWalkWith_eq_of_support (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.Store V)
    (s : Slot) (Hon : Finset V) (B : Block V)
    (hsup : HonestSupport E st.T (confVotes E st s) s Hon B)
    (hvalid : Protocol.VoteSetValid E s (confLate E st s))
    (hpre : Block.Preceq (confAnchorWith contract E hc st) B)
    (hpath : ∀ C : Block V, Block.Preceq (confAnchorWith contract E hc st) C →
      C ≠ confAnchorWith contract E hc st → Block.Preceq C B → C ∈ confTree st) :
    confWalkWith contract E hc st s = B ∧ confEligible E st s B = true := by
  have hN := confNumerator E st s
  have hwalk : confWalkWith contract E hc st s = B := by
    refine ghost_reaches hpre hpath ?_ ?_
    · refine ghost_step_none ?_
      intro C _ hpar
      simp only [confEligible, decide_eq_false_iff_not, confCount, confScore]
      exact hsup.not_eligible hN hvalid (preceq_parent_false hpar)
    · intro H hanch hHB hne
      obtain ⟨C, hpar, hCB⟩ := exists_child_towards B hHB hne
      have hCA : Block.Preceq (confAnchorWith contract E hc st) C :=
        Block.preceq_trans hanch (preceq_of_parent? hpar)
      have hCne : C ≠ confAnchorWith contract E hc st := by
        intro hEq
        have h1 : C.depth = H.depth + 1 := depth_of_parent? hpar
        have h2 : (confAnchorWith contract E hc st).depth ≤ H.depth :=
          Block.preceq_depth_le hanch
        rw [hEq] at h1
        omega
      refine ⟨C, ?_, hCB⟩
      rw [Protocol.ghost_step]
      refine argmax?_eq_some_of_dominates ?_ ?_
      · rw [Protocol.ghost_children, Finset.mem_filter]
        refine ⟨hpath C hCA hCne hCB, hpar, ?_⟩
        simp only [confEligible, decide_eq_true_eq, confCount, confScore]
        exact hsup.eligible hN hvalid hCB
      · intro D hD hDC
        rw [Protocol.ghost_children, Finset.mem_filter] at hD
        have hDB : Block.preceq D B = false := by
          rw [← Bool.not_eq_true]
          intro hpre'
          exact hDC (child_towards_unique hpar hD.2.1 hCB hpre')
        simp only [confScore]
        exact hsup.score_lt hN hvalid hCB hDB
  have helig : confEligible E st s B = true := by
    simp only [confEligible, decide_eq_true_eq, confCount, confScore]
    exact hsup.eligible hN hvalid (Block.preceq_self B)
  exact ⟨hwalk, helig⟩

/-- Under `HonestSupport` for `B`, with `B` a descendant of the confirmation anchor and the path
    from the anchor to `B` in the confirmation tree, the slot-`s` confirmation records `B`. -/
theorem live_confirmed_eq_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.Store V)
    (s : Slot) (Hon : Finset V) (B : Block V)
    (hsup : HonestSupport E st.T (confVotes E st s) s Hon B)
    (hvalid : Protocol.VoteSetValid E s (confLate E st s))
    (hpre : Block.Preceq (confAnchorWith contract E hc st) B)
    (hpath : ∀ C : Block V, Block.Preceq (confAnchorWith contract E hc st) C →
      C ≠ confAnchorWith contract E hc st → Block.Preceq C B → C ∈ confTree st) :
    (Protocol.update_confirmation_with contract E hc st s).live_confirmed = B := by
  obtain ⟨hwalk, helig⟩ :=
    confWalkWith_eq_of_support contract E hc st s Hon B hsup hvalid hpre hpath
  rw [update_confirmation_with_live_confirmed, hwalk, if_pos helig]


end Protocol
end DecoupledConsensusModel

end
