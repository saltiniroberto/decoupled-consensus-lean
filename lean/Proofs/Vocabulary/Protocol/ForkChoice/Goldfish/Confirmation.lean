module
public import Model.Vocabulary.Execution.Setup
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.ForkChoice
public import Mathlib.CategoryTheory.Category.Basic
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# The confirmation count

The confirmation numerator is the early vote set filtered by "the late set holds no second vote by
this validator", so it holds at most one vote per validator and its Goldfish score is the plain
supporter count. From this, two blocks that pass the confirmation test at two nodes in the same slot
are compatible (`eligible_compatible`), and under `HonestSupport` every ancestor of `B` passes the
test while no other block does.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The two cutoffs -/

omit [DecidableEq V] [Fintype V] in
/-- `beforeCutoff` is monotone in the cutoff: a later cutoff keeps more of `S`. -/
theorem beforeCutoff_mono {α : Type} [DecidableEq α] (ts : TimestampMap α)
    {Γ Γ' : Time} (h : Γ ≤ Γ') (S : Finset α) :
    beforeCutoff ts Γ S ⊆ beforeCutoff ts Γ' S := by
  intro x hx
  rw [beforeCutoff, Finset.mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have hs := hx.2
  unfold stampedBefore at hs ⊢
  cases hts : ts x with
  | none =>
      rw [hts] at hs
      exact absurd hs (by simp)
  | some u =>
      rw [hts] at hs
      simp only [decide_eq_true_eq] at hs ⊢
      exact lt_of_lt_of_le hs (WithBot.coe_le_coe.mpr h)

/-- The support cutoff of slot `s` is at most its confirmation time. -/
theorem support_cutoff_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.confirmation_time E s := by
  have key : ∀ a d : Int, 0 ≤ d → a + 2 * d ≤ a + 6 * d := by
    intro a d hd; omega
  exact key (E.t s) E.Δ (le_of_lt E.Δ_pos)

/-! ## The numerator has at most one vote per validator -/

/-- The shape of the confirmation numerator `votes`: the early set filtered by "the late set holds
    no second vote by this validator", with `early ⊆ late`. -/
structure Numerator (early late votes : Finset (GoldfishVote V)) : Prop where
  /-- The early set is contained in the late set. -/
  early_late : early ⊆ late
  /-- The numerator is the early set filtered by the no-second-vote test against the late set. -/
  filtered : votes = early.filter (fun u => Protocol.no_second_vote_in late u = true)

namespace Numerator

variable {early late votes : Finset (GoldfishVote V)}

omit [Fintype V] in
/-- The numerator is inside the early set. -/
theorem subset_early (h : Numerator early late votes) : votes ⊆ early := by
  rw [h.filtered]; exact Finset.filter_subset _ _

omit [Fintype V] in
/-- The numerator is inside the late set. -/
theorem subset_late (h : Numerator early late votes) : votes ⊆ late :=
  subset_trans h.subset_early h.early_late

omit [Fintype V] in
/-- A counted vote is its validator's only vote in the late set: any vote in `late` by the same
    validator is that vote. -/
theorem unique_in_late (h : Numerator early late votes) {u u' : GoldfishVote V}
    (hu : u ∈ votes) (hu' : u' ∈ late) (hval : u'.val_index = u.val_index) : u' = u := by
  rw [h.filtered, Finset.mem_filter] at hu
  have := hu.2
  rw [Protocol.no_second_vote_in, decide_eq_true_eq] at this
  rcases this u' hu' with hEq | hNe
  · exact hEq
  · exact absurd hval hNe

omit [Fintype V] in
/-- A validator has at most one counted vote. -/
theorem votes_by_card_le_one (h : Numerator early late votes) (x : V) :
    (Protocol.votes_by votes x).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro a ha b hb
  rw [Protocol.votes_by, Finset.mem_filter] at ha hb
  exact h.unique_in_late hb.1 (h.subset_late ha.1) (by rw [ha.2, hb.2])

omit [Fintype V] in
/-- No validator equivocates in the numerator. -/
theorem no_equivocation (h : Numerator early late votes) (x : V) :
    Protocol.equivocates votes x = false := by
  rw [Protocol.equivocates, decide_eq_false_iff_not]
  have := h.votes_by_card_le_one x
  omega

omit [Fintype V] in
/-- A validator with a vote in the numerator does not equivocate in the late set. -/
theorem no_equivocation_in_late (h : Numerator early late votes)
    {u : GoldfishVote V} (hu : u ∈ votes) :
    Protocol.equivocates late u.val_index = false := by
  rw [Protocol.equivocates, decide_eq_false_iff_not]
  intro htwo
  have hle : (Protocol.votes_by late u.val_index).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro a ha b hb
    rw [Protocol.votes_by, Finset.mem_filter] at ha hb
    have hau : a = u := h.unique_in_late hu ha.1 ha.2
    have hbu : b = u := h.unique_in_late hu hb.1 hb.2
    exact hau.trans hbu.symm
  omega

/-- With the numerator as both vote arguments, the Goldfish score of `B` is the number of its
    supporters. -/
theorem score_eq_supporters (h : Numerator early late votes) (E : Env V)
    (T : Finset (Block V)) (s : Slot) (B : Block V) :
    Protocol.goldfish_score E T votes votes s B =
      (Protocol.goldfishSupporters E T votes votes s B).card := by
  rw [Protocol.goldfish_score, Protocol.raw_goldfish_score]
  have hempty : Protocol.raw_equivocators votes = ∅ := by
    rw [Protocol.raw_equivocators, Finset.filter_eq_empty_iff]
    intro x _
    rw [h.no_equivocation x]
    simp
  rw [hempty, Finset.card_empty, Nat.zero_add, Protocol.goldfishSupporters]

end Numerator

/-! ## Supporters -/

omit [Fintype V] in
/-- The supporter test `targets_under`, unfolded. -/
theorem targets_under_iff {T : Finset (Block V)} {B : Block V} {u : GoldfishVote V} :
    Protocol.targets_under T B u = true ↔
      ∃ B', Block.find? T u.head = some B' ∧ B'.slot ≤ u.slot ∧
        Block.preceq B B' = true := by
  unfold Protocol.targets_under
  cases hfind : Block.find? T u.head with
  | none => simp
  | some B' => simp

/-- Membership in `goldfishSupporters`, unfolded: the equivocation test reads `votes`, and the vote
    itself comes from `support_votes`. -/
theorem mem_supporters_iff {E : Env V} {T : Finset (Block V)}
    {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} {x : V} :
    x ∈ Protocol.goldfishSupporters E T votes support_votes s B ↔
      Protocol.equivocates votes x = false ∧
      ∃ u ∈ Protocol.votes_by support_votes x, u.slot = s ∧
        Protocol.targets_under T B u = true := by
  simp only [Protocol.goldfishSupporters, Protocol.raw_supporters, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Every supporter of `B` supports every ancestor `C` of `B`. -/
theorem supporters_mono (E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) {C B : Block V}
    (h : Block.preceq C B = true) :
    Protocol.goldfishSupporters E T votes support_votes s B ⊆
      Protocol.goldfishSupporters E T votes support_votes s C := by
  intro x hx
  rw [mem_supporters_iff] at hx ⊢
  obtain ⟨hne, u, hu, hslot, htar⟩ := hx
  obtain ⟨B', hfind, hpre⟩ := targets_under_iff.mp htar
  exact ⟨hne, u, hu, hslot, targets_under_iff.mpr
    ⟨B', hfind, hpre.1, Block.preceq_trans h hpre.2⟩⟩

/-- Every supporter of `B` is a participant of any vote set `late'` that contains the support votes. -/
theorem supporters_subset_participants (E : Env V) (T : Finset (Block V))
    {votes support_votes late' : Finset (GoldfishVote V)}
    (hsub : support_votes ⊆ late') (s : Slot) (B : Block V) :
    Protocol.goldfishSupporters E T votes support_votes s B ⊆
      Protocol.participants E late' s := by
  intro x hx
  rw [mem_supporters_iff] at hx
  obtain ⟨-, u, hu, -, -⟩ := hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hsub hu.1, hu.2⟩

/-- In a valid slot-`s` vote set, the number of participants is at most the size of the slot-`s`
    committee. -/
theorem voters_count_le_committee (E : Env V) (late : Finset (GoldfishVote V))
    (s : Slot) (hvalid : Protocol.VoteSetValid E s late) :
    Protocol.voters_count E late s ≤ (E.committee s).card := by
  rw [Protocol.voters_count,
    Protocol.raw_voters_count_eq_committee_voters_count hvalid,
    Protocol.committee_voters_count]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-! ## Safety: conflicting blocks cannot both pass the confirmation test -/

/-- What one node's confirmation count needs from another's: every vote counted at `v` reaches `w`'s
    late view or `w` already sees its validator equivocate, and the two trees resolve each counted
    vote's head to the same block. -/
structure CrossView (Tv Tw : Finset (Block V)) (votesv latew : Finset (GoldfishVote V)) :
    Prop where
  /-- A counted vote reaches the other late view, or that view already holds an
  equivocation by the vote's validator. -/
  transfer : ∀ u ∈ votesv,
    u ∈ latew ∨ Protocol.equivocates latew u.val_index = true
  /-- The two trees agree whenever both resolve a counted vote's target. -/
  resolve : ∀ u ∈ votesv, ∀ B C : Block V,
    Block.find? Tv u.head = some B → Block.find? Tw u.head = some C → B = C

namespace CrossView

omit [Fintype V] in
/-- `CrossView` follows from the vote transfer condition and root injectivity on `Tv ∪ Tw`. -/
theorem of_rootInjective {Tv Tw : Finset (Block V)}
    {votesv latew : Finset (GoldfishVote V)}
    (transfer : ∀ u ∈ votesv,
      u ∈ latew ∨ Protocol.equivocates latew u.val_index = true)
    (root_injective : RootInjectiveBelow (Tv ∪ Tw)) :
    CrossView Tv Tw votesv latew := by
  refine ⟨transfer, ?_⟩
  intro u _ B C hfindB hfindC
  have hBroot : B.root = u.head := by
    unfold Block.find? pickUnique? at hfindB
    split at hfindB
    · rename_i hex
      rw [Option.some_inj] at hfindB
      subst hfindB
      exact of_decide_eq_true (Finset.choose_property _ _ hex)
    · exact absurd hfindB (by simp)
  have hCroot : C.root = u.head := by
    unfold Block.find? pickUnique? at hfindC
    split at hfindC
    · rename_i hex
      rw [Option.some_inj] at hfindC
      subst hfindC
      exact of_decide_eq_true (Finset.choose_property _ _ hex)
    · exact absurd hfindC (by simp)
  apply root_injective B C
  · exact ⟨B, Finset.mem_union_left Tw (Proofs.Engine.pickUnique?_mem hfindB),
      Block.preceq_self B⟩
  · exact ⟨C, Finset.mem_union_right Tv (Proofs.Engine.pickUnique?_mem hfindC),
      Block.preceq_self C⟩
  · exact hBroot.trans hCroot.symm

end CrossView

/-- Supporters of conflicting blocks `C` and `D`, counted at two different nodes, are disjoint. -/
theorem supporters_disjoint_cross {E : Env V} {Tv Tw : Finset (Block V)}
    {votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V} (hNw : Numerator earlyw latew votesw)
    (hvw : CrossView Tv Tw votesv latew) (hconf : Block.compatible C D = false) :
    Disjoint (Protocol.goldfishSupporters E Tv votesv votesv s C)
      (Protocol.goldfishSupporters E Tw votesw votesw s D) := by
  rw [Finset.disjoint_left]
  intro x hxC hxD
  rw [mem_supporters_iff] at hxC hxD
  obtain ⟨-, u, hu, -, htarC⟩ := hxC
  obtain ⟨-, u', hu', -, htarD⟩ := hxD
  rw [Protocol.votes_by, Finset.mem_filter] at hu hu'
  have hsame : u = u' := by
    rcases hvw.transfer u hu.1 with hreach | hequiv
    · exact hNw.unique_in_late hu'.1 hreach (by rw [hu.2, hu'.2])
    · have hclean := hNw.no_equivocation_in_late hu'.1
      rw [hu'.2] at hclean
      rw [hu.2, hclean] at hequiv
      simp at hequiv
  obtain ⟨B₁, hfind₁, hpre₁⟩ := targets_under_iff.mp htarC
  obtain ⟨B₂, hfind₂, hpre₂⟩ := targets_under_iff.mp htarD
  have hblocks : B₁ = B₂ := by
    apply hvw.resolve u hu.1 B₁ B₂ hfind₁
    simpa only [hsame] using hfind₂
  have : B₂ = B₁ := hblocks.symm
  subst this
  exact absurd (Block.compatible_of_preceq_common hpre₁.2 hpre₂.2) (by rw [hconf]; simp)

/-- Every supporter of `C` counted at the source node is a participant of the target's late view. -/
theorem supporters_subset_participants_cross {E : Env V} {Tv Tw : Finset (Block V)}
    {votesv latew : Finset (GoldfishVote V)} {s : Slot} {C : Block V}
    (hvw : CrossView Tv Tw votesv latew) :
    Protocol.goldfishSupporters E Tv votesv votesv s C ⊆ Protocol.participants E latew s := by
  intro x hx
  rw [mem_supporters_iff] at hx
  obtain ⟨-, u, hu, -, -⟩ := hx
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  rcases hvw.transfer u hu.1 with hreach | hequiv
  · refine Finset.card_pos.mpr ⟨u, ?_⟩
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨hreach, hu.2⟩
  · rw [Protocol.equivocates, decide_eq_true_eq] at hequiv
    rw [hu.2] at hequiv
    omega

/-- The supporters of two conflicting blocks, counted at two nodes, together number at most the
    participants of `w`'s late view. -/
theorem card_supporters_add_le {E : Env V} {Tv Tw : Finset (Block V)}
    {votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V} (hNw : Numerator earlyw latew votesw)
    (hvw : CrossView Tv Tw votesv latew) (hconf : Block.compatible C D = false) :
    (Protocol.goldfishSupporters E Tv votesv votesv s C).card +
        (Protocol.goldfishSupporters E Tw votesw votesw s D).card ≤
      Protocol.voters_count E latew s := by
  have hdisj : Disjoint (Protocol.goldfishSupporters E Tv votesv votesv s C)
      (Protocol.goldfishSupporters E Tw votesw votesw s D) :=
    supporters_disjoint_cross hNw hvw hconf
  rw [← Finset.card_union_of_disjoint hdisj]
  refine Finset.card_le_card ?_
  refine Finset.union_subset ?_ ?_
  · exact supporters_subset_participants_cross hvw
  · exact supporters_subset_participants E Tw hNw.subset_late s D

/-- Two blocks that pass the confirmation test at two nodes in the same slot are compatible. -/
theorem eligible_compatible {E : Env V} {Tv Tw : Finset (Block V)}
    {earlyv latev votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V} (hNv : Numerator earlyv latev votesv)
    (hNw : Numerator earlyw latew votesw)
    (hvw : CrossView Tv Tw votesv latew) (hwv : CrossView Tw Tv votesw latev)
    (hC : Protocol.voters_count E latev s < 2 * Protocol.goldfish_score E Tv votesv votesv s C)
    (hD : Protocol.voters_count E latew s < 2 * Protocol.goldfish_score E Tw votesw votesw s D) :
    Block.compatible C D = true := by
  by_contra hcon
  have hconf : Block.compatible C D = false := by simpa using hcon
  have hconf' : Block.compatible D C = false := by
    rw [Block.compatible, Bool.or_eq_false_iff]
    rw [Block.compatible, Bool.or_eq_false_iff] at hconf
    exact ⟨hconf.2, hconf.1⟩
  rw [hNv.score_eq_supporters] at hC
  rw [hNw.score_eq_supporters] at hD
  have h₁ := card_supporters_add_le (E := E) (s := s) hNw hvw hconf
  have h₂ := card_supporters_add_le (E := E) (s := s) hNv hwv hconf'
  omega

/-! ## Liveness: every ancestor of an honestly supported block passes the confirmation test -/

/-- The honest members of the slot-`s` committee are a strict majority of it, and each has a counted
    slot-`s` vote resolving to `B`. -/
structure HonestSupport (E : Env V) (T : Finset (Block V))
    (votes : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) (B : Block V) : Prop where
  /-- The honest committee members are a strict majority: `|K_s| < 2·|K_s ∩ H|`. -/
  majority : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card
  /-- Every honest committee member's counted slot-`s` vote resolves to `B`. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ votes, u.val_index = x ∧ u.slot = s ∧
    Block.find? T u.head = some B ∧ B.slot ≤ u.slot

namespace HonestSupport

variable {E : Env V} {T : Finset (Block V)}
  {early late votes : Finset (GoldfishVote V)} {s : Slot} {Hon : Finset V} {B : Block V}

/-- Every honest committee member supports every ancestor of `B`. -/
theorem subset_supporters (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) {C : Block V}
    (hC : Block.preceq C B = true) :
    (E.committee s) ∩ Hon ⊆ Protocol.goldfishSupporters E T votes votes s C := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, hslot, hfind, hBslot⟩ := h.vote x hx.1 hx.2
  rw [mem_supporters_iff]
  refine ⟨hN.no_equivocation x, u, ?_, hslot,
    targets_under_iff.mpr ⟨B, hfind, hBslot, hC⟩⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hu, hval⟩

/-- No honest committee member supports a block `D` that is not an ancestor of `B`. -/
theorem not_mem_supporters (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) {D : Block V}
    (hD : Block.preceq D B = false) {x : V} (hx : x ∈ E.committee s) (hxH : x ∈ Hon) :
    x ∉ Protocol.goldfishSupporters E T votes votes s D := by
  intro hmem
  rw [mem_supporters_iff] at hmem
  obtain ⟨-, u', hu', -, htar⟩ := hmem
  obtain ⟨u, hu, hval, -, hfind, -⟩ := h.vote x hx hxH
  rw [Protocol.votes_by, Finset.mem_filter] at hu'
  have hsame : u' = u := hN.unique_in_late hu (hN.subset_late hu'.1) (by rw [hu'.2, hval])
  obtain ⟨B', hfind', hpre⟩ := targets_under_iff.mp htar
  rw [hsame, hfind] at hfind'
  have : B' = B := by simpa using hfind'.symm
  subst this
  exact absurd hpre.2 (by rw [hD]; simp)

/-- The honest committee members are counted in the denominator. -/
theorem inter_subset_participants (h : HonestSupport E T votes s Hon B)
    (hsub : votes ⊆ late) : (E.committee s) ∩ Hon ⊆ Protocol.participants E late s := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, -, -, -⟩ := h.vote x hx.1 hx.2
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hsub hu, hval⟩

/-- Every ancestor `C` of `B` passes the confirmation test: `count < 2·score(C)`. -/
theorem eligible (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {C : Block V}
    (hC : Block.preceq C B = true) :
    Protocol.voters_count E late s < 2 * Protocol.goldfish_score E T votes votes s C := by
  have hscore : ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes votes s C := by
    rw [hN.score_eq_supporters]
    exact Finset.card_le_card (h.subset_supporters hN hC)
  have hcount := voters_count_le_committee E late s hvalid
  have := h.majority
  omega

/-- A block that is not an ancestor of `B` is supported only by Byzantine participants. -/
theorem score_le_byz (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {D : Block V}
    (hD : Block.preceq D B = false) :
    Protocol.goldfish_score E T votes votes s D ≤
      ((Protocol.participants E late s) \ Hon).card := by
  rw [hN.score_eq_supporters]
  refine Finset.card_le_card ?_
  intro x hx
  have hx' := hx
  rw [mem_supporters_iff] at hx'
  refine Finset.mem_sdiff.mpr ⟨supporters_subset_participants E T hN.subset_late s D hx, ?_⟩
  intro hxH
  obtain ⟨-, u, hu, -, -⟩ := hx'
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  have hcommittee := (hvalid u (hN.subset_late hu.1)).2
  rw [hu.2] at hcommittee
  exact h.not_mem_supporters hN hD hcommittee hxH hx

/-- The Byzantine participants are fewer than the honest committee members. -/
theorem byz_lt (h : HonestSupport E T votes s Hon B)
    (hvalid : Protocol.VoteSetValid E s late) :
    ((Protocol.participants E late s) \ Hon).card < ((E.committee s) ∩ Hon).card := by
  have hsub : (Protocol.participants E late s) \ Hon ⊆ (E.committee s) \ Hon := by
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    have hx' : x ∈ Protocol.committee_participants E late s := by
      rw [← Protocol.raw_participants_eq_committee_participants hvalid]
      exact hx.1
    exact ⟨Finset.filter_subset _ _ hx', hx.2⟩
  have hcard : ((E.committee s) \ Hon).card =
      (E.committee s).card - ((E.committee s) ∩ Hon).card := by
    rw [Finset.card_sdiff, Finset.inter_comm]
  have hle := Finset.card_le_card hsub
  have hinter : ((E.committee s) ∩ Hon).card ≤ (E.committee s).card :=
    Finset.card_le_card Finset.inter_subset_left
  have := h.majority
  omega

/-- A block that is not an ancestor of `B` has a strictly smaller score than every ancestor of `B`. -/
theorem score_lt (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {C D : Block V}
    (hC : Block.preceq C B = true) (hD : Block.preceq D B = false) :
    Protocol.goldfish_score E T votes votes s D < Protocol.goldfish_score E T votes votes s C := by
  have h₁ := h.score_le_byz (late := late) hN hvalid hD
  have h₂ : ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes votes s C := by
    rw [hN.score_eq_supporters]
    exact Finset.card_le_card (h.subset_supporters hN hC)
  have h₃ := h.byz_lt (late := late) hvalid
  omega

/-- A block that is not an ancestor of `B` fails the confirmation test. -/
theorem not_eligible (h : HonestSupport E T votes s Hon B)
    (hN : Numerator early late votes) (hvalid : Protocol.VoteSetValid E s late)
    {D : Block V}
    (hD : Block.preceq D B = false) :
    ¬ Protocol.voters_count E late s < 2 * Protocol.goldfish_score E T votes votes s D := by
  have h₁ := h.score_le_byz (late := late) hN hvalid hD
  have h₃ := h.byz_lt (late := late) hvalid
  have hsplit : ((E.committee s) ∩ Hon).card + ((Protocol.participants E late s) \ Hon).card ≤
      Protocol.voters_count E late s := by
    have hdisj : Disjoint ((E.committee s) ∩ Hon)
        ((Protocol.participants E late s) \ Hon) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_inter.mp hx).2
    rw [Protocol.voters_count, ← Finset.card_union_of_disjoint hdisj]
    refine Finset.card_le_card (Finset.union_subset ?_ Finset.sdiff_subset)
    exact h.inter_subset_participants hN.subset_late
  omega

end HonestSupport

end Protocol
end DecoupledConsensusModel

end
