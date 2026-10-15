module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# Confirmation adoption by the next Goldfish voters

When a block passes the confirmation test at one view, its supporters there become supporters in a
later voter's view and form a strict majority of that view's participants, given
`AdoptionTransport`. The walk of that voter then passes through the block.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Protocol (ChainState)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Transport between two views -/

/-- The delivery facts that carry one confirmation count for `B` into an ordinary voter's view:
    `sourceVotes` and `sourceLate` are the confirmation's numerator and denominator votes,
    `targetVotes` and `targetSupport` the voter's raw and support views. -/
structure AdoptionTransport (sourceTree targetTree : Finset (Block V))
    (sourceVotes sourceLate targetVotes targetSupport : Finset (GoldfishVote V))
    (B : Block V) : Prop where
  /-- Every source vote supporting `B` is in the target support view and still supports `B` there,
      or the target raw view shows its validator equivocating. -/
  forward : ∀ u ∈ sourceVotes,
    Protocol.targets_under sourceTree B u = true →
      (u ∈ targetSupport ∧ Protocol.targets_under targetTree B u = true) ∨
        Protocol.equivocates targetVotes u.val_index = true
  /-- Every target raw vote is in the source late view, or the source late view shows its validator
      equivocating. -/
  backward : ∀ u ∈ targetVotes,
    u ∈ sourceLate ∨ Protocol.equivocates sourceLate u.val_index = true

namespace AdoptionTransport

variable {sourceTree targetTree : Finset (Block V)}
  {sourceVotes sourceEarly sourceLate targetVotes targetSupport : Finset (GoldfishVote V)}
  {B : Block V}

omit [Fintype V] in
/-- The validator of a counted source vote does not equivocate in the target raw view. -/
theorem target_not_equivocates
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B) {u : GoldfishVote V} (hu : u ∈ sourceVotes) :
    Protocol.equivocates targetVotes u.val_index = false := by
  have hcard : (Protocol.votes_by targetVotes u.val_index).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [Protocol.votes_by, Finset.mem_filter] at ha hb
    have vote_eq_source : ∀ {x : GoldfishVote V}, x ∈ targetVotes →
        x.val_index = u.val_index → x = u := by
      intro x hx hval
      rcases hT.backward x hx with hreach | hequiv
      · exact hN.unique_in_late hu hreach hval
      · have hclean := hN.no_equivocation_in_late hu
        rw [hval, hclean] at hequiv
        simp at hequiv
    exact (vote_eq_source ha.1 ha.2).trans (vote_eq_source hb.1 hb.2).symm
  rw [Protocol.equivocates, decide_eq_false_iff_not]
  omega

/-- Every supporter of `B` in the source confirmation count is a supporter of `B` in the target
    view. -/
theorem supporters_subset
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B) (E : Env V) (s : Slot) :
    Protocol.goldfishSupporters E sourceTree sourceVotes sourceVotes s B ⊆
      Protocol.goldfishSupporters E targetTree targetVotes targetSupport s B := by
  intro x hx
  rw [mem_supporters_iff] at hx ⊢
  obtain ⟨-, u, hu, hslot, htarget⟩ := hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  have hclean := hT.target_not_equivocates hN hu.1
  have hcleanX : Protocol.equivocates targetVotes x = false := by
    simpa only [hu.2] using hclean
  rcases hT.forward u hu.1 htarget with hreach | hequiv
  · refine ⟨hcleanX, u, ?_, hslot, hreach.2⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hreach.1, hu.2⟩
  · rw [hclean] at hequiv
    simp at hequiv

/-- Every participant of the target raw view is a participant of the source late view. -/
theorem participants_subset
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B) (E : Env V) (s : Slot) :
    Protocol.participants E targetVotes s ⊆ Protocol.participants E sourceLate s := by
  intro x hx
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx ⊢
  rw [Protocol.participates, decide_eq_true_eq] at hx ⊢
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  rcases hT.backward u hu.1 with hreach | hequiv
  · refine Finset.card_pos.mpr ⟨u, ?_⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hreach, hu.2⟩
  · rw [Protocol.equivocates, decide_eq_true_eq] at hequiv
    rw [hu.2] at hequiv
    omega

end AdoptionTransport

/-! ## Strict-majority adoption -/

/-- If `B` passes the confirmation test in the source views, its source supporters are target
    supporters and form a strict majority of the target participants. -/
theorem confirmation_adoption
    {E : Env V} {sourceTree targetTree : Finset (Block V)}
    {sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)} {s : Slot} {B : Block V}
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (heligible : Protocol.voters_count E sourceLate s <
      2 * Protocol.goldfish_score E sourceTree sourceVotes sourceVotes s B) :
    Protocol.goldfishSupporters E sourceTree sourceVotes sourceVotes s B ⊆
        Protocol.goldfishSupporters E targetTree targetVotes targetSupport s B ∧
      Protocol.voters_count E targetVotes s <
        2 * (Protocol.goldfishSupporters E targetTree targetVotes targetSupport s B).card := by
  have hsupport := AdoptionTransport.supporters_subset hN hT E s
  have hsupport_card := Finset.card_le_card hsupport
  have hparticipants := Finset.card_le_card
    (AdoptionTransport.participants_subset hT E s)
  have hparticipants' : Protocol.voters_count E targetVotes s ≤
      Protocol.voters_count E sourceLate s := by
    simpa only [Protocol.voters_count, Protocol.raw_voters_count,
      Protocol.participants] using hparticipants
  have hsource : Protocol.voters_count E sourceLate s <
      2 * (Protocol.goldfishSupporters E sourceTree sourceVotes sourceVotes s B).card := by
    simpa only [hN.score_eq_supporters] using heligible
  exact ⟨hsupport, by omega⟩


/-! ## A confirmation that passed the test -/

/-- The confirmation update writes `B` to `live_confirmed`, and the confirmation walk's block passes
    the test `confEligible`. -/
structure GenuineConfirmation (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot) (B : Block V)
    (contract : Protocol.GradeContract V) : Prop where
  selected : (Protocol.update_confirmation_with contract E hc st s).live_confirmed = B
  genuine : confEligible E st s (confWalkWith contract E hc st s) = true

namespace GenuineConfirmation

/-- Under `GenuineConfirmation`, `B` is the confirmation walk's block. -/
theorem walk_eq {E : Env V} {hc : Protocol.HealConfig} {st : Protocol.Store V}
    {s : Slot} {B : Block V} {contract : Protocol.GradeContract V}
    (h : GenuineConfirmation E hc st s B (contract := contract)) :
    confWalkWith contract E hc st s = B := by
  have hselected := h.selected
  rw [update_confirmation_with_live_confirmed, if_pos h.genuine] at hselected
  exact hselected

/-- Under `GenuineConfirmation`, `B` passes the confirmation's strict-majority test. -/
theorem eligible {E : Env V} {hc : Protocol.HealConfig} {st : Protocol.Store V}
    {s : Slot} {B : Block V} {contract : Protocol.GradeContract V}
    (h : GenuineConfirmation E hc st s B (contract := contract)) :
    Protocol.voters_count E (confLate E st s) s <
      2 * Protocol.goldfish_score E st.T (confVotes E st s) (confVotes E st s) s B := by
  have hg := h.genuine
  simp only [confEligible, decide_eq_true_eq, confCount, confScore] at hg
  simpa only [h.walk_eq] using hg

end GenuineConfirmation

/-! ## The walk passes through a majority-supported block -/

/-- When `support ⊆ votes`, the supporters of two conflicting blocks are disjoint. -/
theorem supporters_disjoint_of_conflicts
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B D : Block V}
    (hsub : support ⊆ votes) (hconflict : Block.compatible B D = false) :
    Disjoint (Protocol.goldfishSupporters E T votes support s B)
      (Protocol.goldfishSupporters E T votes support s D) := by
  rw [Finset.disjoint_left]
  intro x hxB hxD
  rw [mem_supporters_iff] at hxB hxD
  obtain ⟨hclean, u, hu, -, htargetB⟩ := hxB
  obtain ⟨-, u', hu', -, htargetD⟩ := hxD
  rw [Protocol.votes_by, Finset.mem_filter] at hu hu'
  have hcard : (Protocol.votes_by votes x).card ≤ 1 := by
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hclean
    omega
  have huRaw : u ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hsub hu.1, hu.2⟩
  have huRaw' : u' ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hsub hu'.1, hu'.2⟩
  have hs : u' = u := Finset.card_le_one.mp hcard u' huRaw' u huRaw
  obtain ⟨CB, hfindB, hpreB⟩ := targets_under_iff.mp htargetB
  obtain ⟨CD, hfindD, hpreD⟩ := targets_under_iff.mp htargetD
  rw [hs, hfindB] at hfindD
  have hEq : CD = CB := by simpa using hfindD.symm
  subst hEq
  exact absurd (Block.compatible_of_preceq_common hpreB.2 hpreD.2)
    (by rw [hconflict]; simp)

/-- When `support ⊆ votes` and `B` and `D` conflict, `D`'s score plus the number of `B`'s supporters
    is at most the number of participants. -/
theorem score_add_supporters_le
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B D : Block V}
    (hsub : support ⊆ votes) (hconflict : Block.compatible B D = false) :
    Protocol.goldfish_score E T votes support s D +
        (Protocol.goldfishSupporters E T votes support s B).card ≤
      Protocol.voters_count E votes s := by
  have hdisjScore : Disjoint (Protocol.equivocators E votes s)
      (Protocol.goldfishSupporters E T votes support s D) := by
    rw [Finset.disjoint_left]
    intro x hxEq hxD
    simp only [Protocol.equivocators, Protocol.raw_equivocators,
      Finset.mem_filter, Finset.mem_univ, true_and] at hxEq
    rw [mem_supporters_iff] at hxD
    rw [hxD.1] at hxEq
    simp at hxEq
  have hdisjCandidates : Disjoint
      (Protocol.goldfishSupporters E T votes support s B)
      (Protocol.goldfishSupporters E T votes support s D) :=
    supporters_disjoint_of_conflicts (E := E) (T := T) (s := s) hsub hconflict
  have hdisjAll : Disjoint
      ((Protocol.equivocators E votes s) ∪
        (Protocol.goldfishSupporters E T votes support s D))
      (Protocol.goldfishSupporters E T votes support s B) := by
    rw [Finset.disjoint_left]
    intro x hx hxB
    rw [Finset.mem_union] at hx
    rcases hx with hxEq | hxD
    · have hclean := (mem_supporters_iff.mp hxB).1
      simp only [Protocol.equivocators, Protocol.raw_equivocators,
        Finset.mem_filter, Finset.mem_univ, true_and] at hxEq
      rw [hclean] at hxEq
      simp at hxEq
    · exact (Finset.disjoint_left.mp hdisjCandidates) hxB hxD
  have hparticipants :
      ((Protocol.equivocators E votes s) ∪
        (Protocol.goldfishSupporters E T votes support s D)) ∪
          (Protocol.goldfishSupporters E T votes support s B) ⊆
        Protocol.participants E votes s := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
    · exact Proofs.Optimistic.equivocators_subset_participants E (Finset.Subset.rfl) s
    · exact supporters_subset_participants E T hsub s D
    · exact supporters_subset_participants E T hsub s B
  have hcard := Finset.card_le_card hparticipants
  rw [Finset.card_union_of_disjoint hdisjAll,
    Finset.card_union_of_disjoint hdisjScore] at hcard
  rw [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.voters_count, Protocol.raw_voters_count]
  exact hcard

/-- If `B`'s supporters are a strict majority of the participants, every ancestor `C` of `B`
    outscores every block `D` that conflicts with `B`. -/
theorem score_lt_of_supporter_majority
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B C D : Block V}
    (hsub : support ⊆ votes)
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hCB : Block.preceq C B = true)
    (hconflict : Block.compatible B D = false) :
    Protocol.goldfish_score E T votes support s D <
      Protocol.goldfish_score E T votes support s C := by
  have hfit := score_add_supporters_le (E := E) (T := T) (s := s) hsub hconflict
  have hmono := Finset.card_le_card (supporters_mono E T votes support s hCB)
  have hbelow : Protocol.goldfish_score E T votes support s D <
      (Protocol.goldfishSupporters E T votes support s B).card := by
    omega
  have habove : (Protocol.goldfishSupporters E T votes support s C).card ≤
      Protocol.goldfish_score E T votes support s C := by
    rw [Protocol.goldfish_score, Protocol.raw_goldfish_score, Protocol.goldfishSupporters]
    omega
  omega

/-- If `B`'s supporters are a strict majority of the participants, every ancestor `C` of `B` passes
    the majority test. -/
theorem eligible_of_supporter_majority
    {E : Env V} {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot} {B C : Block V}
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hCB : Block.preceq C B = true) :
    Protocol.voters_count E votes s <
      2 * Protocol.goldfish_score E T votes support s C := by
  have hmono := Finset.card_le_card (supporters_mono E T votes support s hCB)
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.goldfishSupporters] at hmajority hmono ⊢
  omega

/-- If `B`'s supporters are a strict majority of the participants and the anchor `A` is an ancestor
    of `B` whose path to `B` lies in `tree`, the Goldfish fork choice from `A` is `B` or a
    descendant of `B`. -/
theorem goldfish_fork_choice_passes_supporter_majority
    (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hsub : support ⊆ votes)
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
      C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support s) := by
  rw [Protocol.goldfish_fork_choice]
  refine Proofs.Optimistic.ghost_passes hAB hpath ?_
  intro H hAH hHB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHB hne
  have hAC : Block.Preceq A C :=
    Block.preceq_trans hAH (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = H.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ H.depth := Block.preceq_depth_le hAH
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hHlt : H.depth < B.depth := by
    rcases Nat.lt_or_ge H.depth B.depth with h | h
    · exact h
    · exact absurd (Block.preceq_eq_of_depth_le hHB h) hne
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_dominates ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    refine ⟨hCmem, hCpar, ?_⟩
    rw [Proofs.Optimistic.goldfish_eligible_iff]
    exact Or.inr (Or.inl (eligible_of_supporter_majority hmajority hCB))
  · intro D hD hDC
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    have hDpar := hD.2.1
    have hDB : Block.preceq D B = false := by
      rw [← Bool.not_eq_true]
      intro hpre
      exact hDC (child_towards_unique hCpar hDpar hCB hpre)
    have hDdepth : D.depth ≤ B.depth := by
      rw [depth_of_parent? hDpar]
      omega
    have hBD : Block.preceq B D = false := by
      rw [← Bool.not_eq_true]
      intro hpre
      have hEq : B = D := Block.preceq_eq_of_depth_le hpre hDdepth
      rw [← hEq] at hDB
      exact absurd (Block.preceq_self B) (by rw [hDB]; simp)
    have hconflict : Block.compatible B D = false := by
      simp only [Block.compatible, Bool.or_eq_false_iff]
      exact ⟨hBD, hDB⟩
    exact score_lt_of_supporter_majority hsub hmajority hCB hconflict

/-- If `B`'s supporters are a strict majority of the participants and the anchor `A` is compatible
    with `B`, with the path to `B` in `tree` when `A` is an ancestor of `B`, the Goldfish fork
    choice from `A` is `B` or a descendant of `B`. -/
theorem goldfish_fork_choice_captures_supporter_majority
    (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hsub : support ⊆ votes)
    (hmajority : Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support s) := by
  simp only [Block.compatible, Bool.or_eq_true] at hcompatible
  rcases hcompatible with hAB | hBA
  · exact goldfish_fork_choice_passes_supporter_majority E σ h_max T tree cur
      votes support s hsub hmajority hAB (hpath hAB)
  · rw [Protocol.goldfish_fork_choice]
    exact Block.preceq_trans hBA
      (ghost_preceq A tree (Protocol.goldfish_score E T votes support s)
        (Protocol.goldfish_eligible E σ h_max T cur votes support s))


/-- If `B` passes the confirmation test in the source views, `AdoptionTransport` holds, and the
    anchor `A` is compatible with `B` (with the path to `B` in `tree` when `A` is an ancestor of
    `B`), the target view's Goldfish fork choice from `A` is `B` or a descendant of `B`. -/
theorem goldfish_fork_choice_captures_of_confirmation
    (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (sourceTree targetTree tree : Finset (Block V)) (cur : Slot)
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree targetTree sourceVotes sourceLate
      targetVotes targetSupport B)
    (heligible : Protocol.voters_count E sourceLate s <
      2 * Protocol.goldfish_score E sourceTree sourceVotes sourceVotes s B)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B →
      ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B →
        C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max targetTree cur A tree
        targetVotes targetSupport s) := by
  exact goldfish_fork_choice_captures_supporter_majority E σ h_max targetTree tree cur
    targetVotes targetSupport s hsub (confirmation_adoption hN hT heligible).2
    hcompatible hpath


end Protocol
end DecoupledConsensusModel

end
