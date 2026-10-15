module
public import Proofs.Vocabulary.Protocol.Grades.Main
public import Proofs.Vocabulary.Internal.Definitions.NamedLifecycle
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedHeadReads
public import Proofs.Vocabulary.ModelProperties.NamedDuties_goldfish_vote_with
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
import Mathlib.Tactic.ENatToNat

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol
open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Cones -/


omit [Fintype V] in
/-- If `C ⪯ B`, `C ≠ B` and `B`'s parent is `H`, then `C ⪯ H`. -/
theorem preceq_parent_of_ne {C B H : Block V} (hpar : B.parent? = some H)
    (hCB : Block.preceq C B = true) (hne : C ≠ B) : Block.preceq C H = true := by
  cases B with
  | genesis => simp [Block.parent?] at hpar
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent?, Option.some.injEq] at hpar
      subst hpar
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hCB
      rcases hCB with h | h
      · exact absurd h hne
      · exact h

/-- Every block `tgt` admits is `C` or a descendant of `C`. -/
def Under (tgt : Block V → Prop) (C : Block V) : Prop :=
  ∀ X : Block V, tgt X → Block.preceq C X = true

/-- No block `tgt` admits is `D` or a descendant of `D`. -/
def Off (tgt : Block V → Prop) (D : Block V) : Prop :=
  ∀ X : Block V, tgt X → Block.preceq D X = false

omit [Fintype V] in
/-- A block `D` that is not an ancestor of `B` and has depth at most `B`'s is an ancestor of no
    descendant of `B`. -/
theorem off_of_depth {B D : Block V} (hD : Block.preceq D B = false)
    (hdep : D.depth ≤ B.depth) : Off (fun X => Block.Preceq B X) D := by
  intro X hBX
  rw [← Bool.not_eq_true]
  intro hDX
  rcases Block.preceq_linear hDX hBX with h | h
  · exact absurd h (by rw [hD]; simp)
  · have hEq : B = D := Block.preceq_eq_of_depth_le h hdep
    rw [← hEq] at hD
    exact absurd (Block.preceq_self B) (by rw [hD]; simp)


/-! ## Honest support with equivocators -/

/-- When `votes ⊆ late`, every equivocator of `votes` is a participant of `late`. -/
theorem equivocators_subset_participants (E : Env V)
    {votes late : Finset (GoldfishVote V)} (hsub : votes ⊆ late) (s : Slot) :
    Protocol.equivocators E votes s ⊆ Protocol.participants E late s := by
  intro x hx
  simp only [Protocol.equivocators, Protocol.raw_equivocators, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hcard : 2 ≤ (Protocol.votes_by votes x).card := by
    have := hx
    rw [Protocol.equivocates, decide_eq_true_eq] at this
    exact this
  have hmono : (Protocol.votes_by votes x).card ≤ (Protocol.votes_by late x).card := by
    refine Finset.card_le_card ?_
    intro u hu
    rw [Protocol.votes_by, Finset.mem_filter] at hu ⊢
    exact ⟨hsub hu.1, hu.2⟩
  rw [Protocol.participates, decide_eq_true_eq]
  omega

/-- Honest support for a cone `tgt` of targets at slot `s`: the honest committee members are a
    strict majority of the committee, the counted votes are within the denominator's votes, the
    support votes are within the raw votes, no honest committee member equivocates, and each casts a
    support vote naming a block `tgt` admits. -/
structure ConeSupport (E : Env V) (T : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    (tgt : Block V → Prop) : Prop where
  /-- `|K_s| < 2·|K_s ∩ Hon|`. -/
  majority : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card
  /-- The counted votes are within the denominator's votes. -/
  counted : votes ⊆ late
  /-- The support votes are within the raw votes. -/
  sub : support ⊆ votes
  /-- No honest committee member equivocates in the raw votes. -/
  no_equiv : ∀ x ∈ E.committee s, x ∈ Hon → Protocol.equivocates votes x = false
  /-- Every honest committee member has a slot-`s` support vote whose head resolves in `T` to a
      block of its slot or earlier that `tgt` admits. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧
    ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X

namespace ConeSupport

variable {E : Env V} {T : Finset (Block V)}
  {votes support late : Finset (GoldfishVote V)}
  {s : Slot} {Hon : Finset V} {tgt : Block V → Prop}

/-- Every honest committee member supports every block `C` the cone lies under. -/
theorem subset_supporters (h : ConeSupport E T votes support late s Hon tgt)
    {C : Block V} (hC : Under tgt C) :
    (E.committee s) ∩ Hon ⊆ Protocol.goldfishSupporters E T votes support s C := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, hslot, X, hfind, hXslot, htgt⟩ := h.vote x hx.1 hx.2
  rw [mem_supporters_iff]
  refine ⟨h.no_equiv x hx.1 hx.2, u, ?_, hslot,
    targets_under_iff.mpr ⟨X, hfind, hXslot, hC X htgt⟩⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hu, hval⟩

/-- Every honest committee member is a participant of the denominator's votes. -/
theorem subset_participants (h : ConeSupport E T votes support late s Hon tgt) :
    (E.committee s) ∩ Hon ⊆ Protocol.participants E late s := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, -, -⟩ := h.vote x hx.1 hx.2
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨h.counted (h.sub hu), hval⟩

/-- No honest committee member supports a block `D` off the cone. -/
theorem not_mem_supporters (h : ConeSupport E T votes support late s Hon tgt)
    {D : Block V}
    (hD : Off tgt D) {x : V} (hx : x ∈ E.committee s) (hxH : x ∈ Hon) :
    x ∉ Protocol.goldfishSupporters E T votes support s D := by
  intro hmem
  rw [mem_supporters_iff] at hmem
  obtain ⟨-, u', hu', -, htar⟩ := hmem
  obtain ⟨u, hu, hval, -, X, hfind, hXslot, htgt⟩ := h.vote x hx hxH
  have hcard : (Protocol.votes_by votes x).card ≤ 1 := by
    have hne := h.no_equiv x hx hxH
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hne
    omega
  have huin : u ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨h.sub hu, hval⟩
  have hu'raw : u' ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter] at hu' ⊢
    exact ⟨h.sub hu'.1, hu'.2⟩
  have hsame : u' = u := Finset.card_le_one.mp hcard u' hu'raw u huin
  obtain ⟨Y, hfindY, hpre⟩ := targets_under_iff.mp htar
  rw [hsame, hfind] at hfindY
  have hYX : Y = X := by simpa using hfindY.symm
  subst hYX
  exact absurd hpre.2 (by rw [hD Y htgt]; simp)

/-- The score of a block `D` off the cone plus the number of honest committee members is at most the
    number of participants. -/
theorem score_add_le (h : ConeSupport E T votes support late s Hon tgt) {D : Block V}
    (hD : Off tgt D) :
    Protocol.goldfish_score E T votes support s D + ((E.committee s) ∩ Hon).card ≤
      Protocol.voters_count E late s := by
  have hdisj1 : Disjoint (Protocol.equivocators E votes s)
      (Protocol.goldfishSupporters E T votes support s D) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Protocol.equivocators, Protocol.raw_equivocators, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rw [mem_supporters_iff] at hx'
    rw [hx'.1] at hx
    simp at hx
  have hdisj2 : Disjoint ((Protocol.equivocators E votes s) ∪
      (Protocol.goldfishSupporters E T votes support s D)) ((E.committee s) ∩ Hon) := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_union]
    rintro (hx' | hx')
    · simp only [Protocol.equivocators, Protocol.raw_equivocators,
        Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      rw [h.no_equiv x hx.1 hx.2] at hx'
      simp at hx'
    · exact h.not_mem_supporters hD hx.1 hx.2 hx'
  have hsub : ((Protocol.equivocators E votes s) ∪
      (Protocol.goldfishSupporters E T votes support s D)) ∪ ((E.committee s) ∩ Hon) ⊆
      Protocol.participants E late s := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) h.subset_participants
    · exact equivocators_subset_participants E h.counted s
    · exact supporters_subset_participants E T (subset_trans h.sub h.counted) s D
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1] at hcard
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.equivocators, Protocol.goldfishSupporters, Protocol.voters_count,
    Protocol.raw_voters_count, Protocol.participants] at hcard ⊢
  omega

/-- On a valid vote set, the number of participants is less than twice the number of honest
    committee members. -/
theorem count_lt (h : ConeSupport E T votes support late s Hon tgt) :
    Protocol.VoteSetValid E s late →
    Protocol.voters_count E late s < 2 * ((E.committee s) ∩ Hon).card := by
  intro hvalid
  have h1 := voters_count_le_committee E late s hvalid
  have h2 := h.majority
  omega

/-- A block `C` the cone lies under scores at least the number of honest committee members. -/
theorem le_score (h : ConeSupport E T votes support late s Hon tgt) {C : Block V}
    (hC : Under tgt C) :
    ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes support s C := by
  have hle := Finset.card_le_card (h.subset_supporters hC)
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.goldfishSupporters] at hle ⊢
  omega

/-- On a valid vote set, a block `C` the cone lies under passes the majority test. -/
theorem eligible (h : ConeSupport E T votes support late s Hon tgt) {C : Block V}
    (hvalid : Protocol.VoteSetValid E s late) (hC : Under tgt C) :
    Protocol.voters_count E late s <
      2 * Protocol.goldfish_score E T votes support s C := by
  have h1 := h.count_lt hvalid
  have h2 := h.le_score hC
  omega

/-- On a valid vote set, a block `D` off the cone fails the majority test. -/
theorem not_eligible (h : ConeSupport E T votes support late s Hon tgt) {D : Block V}
    (hvalid : Protocol.VoteSetValid E s late) (hD : Off tgt D) :
    ¬ Protocol.voters_count E late s <
      2 * Protocol.goldfish_score E T votes support s D := by
  have h1 := h.count_lt hvalid
  have h2 := h.score_add_le hD
  omega

/-- On a valid vote set, a block `D` off the cone scores less than every block `C` the cone lies
    under. -/
theorem score_lt (h : ConeSupport E T votes support late s Hon tgt) {C D : Block V}
    (hvalid : Protocol.VoteSetValid E s late) (hC : Under tgt C) (hD : Off tgt D) :
    Protocol.goldfish_score E T votes support s D <
      Protocol.goldfish_score E T votes support s C := by
  have h1 := h.count_lt hvalid
  have h2 := h.score_add_le hD
  have h3 := h.le_score hC
  omega

end ConeSupport


/-! ## Facts about the walk -/

omit [Fintype V] in
/-- If `C` is the only member of `children`, `argmax?` over `children` returns `C`. -/
theorem argmax?_eq_some_of_unique {score : Block V → Nat} {children : Finset (Block V)}
    {C : Block V} (hC : C ∈ children) (huniq : ∀ D ∈ children, D = C) :
    Protocol.argmax? score children = some C := by
  refine pickUnique?_eq_some hC ?_ (fun a ha _ => huniq a ha)
  simp only [Protocol.is_best_in, decide_eq_true_eq]
  intro D hD
  rw [huniq D hD]
  simp [Protocol.outranks]


omit [Fintype V] in

/-- If every step from a block `H` with `anchor ⪯ H ⪯ target` and `H ≠ target` lands on an ancestor
    of `target`, a walk from such an `H` with fuel at least `target.depth − H.depth` ends at
    `target` or a descendant of `target`. -/
theorem ghost_walk_passes {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    ∀ (n : Nat) (H : Block V), Block.Preceq anchor H → Block.Preceq H target →
      target.depth ≤ H.depth + n →
      Block.Preceq target (Protocol.ghost_walk tree score eligible n H) := by
  intro n
  induction n with
  | zero =>
      intro H _ hpre hd
      have hEq : H = target := Block.preceq_eq_of_depth_le hpre (by omega)
      simp only [Protocol.ghost_walk, hEq]
      exact Block.preceq_self _
  | succ n ih =>
      intro H hanch hpre hd
      by_cases hHt : H = target
      · subst hHt
        exact ghost_walk_preceq tree score eligible (n + 1) H
      · obtain ⟨C, hCs, hCp⟩ := hstep H hanch hpre hHt
        have hchild := ghost_step_child hCs
        have hdepth : C.depth = H.depth + 1 := depth_of_parent? hchild.2.1
        simp only [Protocol.ghost_walk, hCs]
        exact ih C (Block.preceq_trans hanch (preceq_of_parent? hchild.2.1)) hCp (by omega)

omit [Fintype V] in

/-- If `anchor ⪯ target`, the path between them is in `tree`, and every step from an ancestor
    `H ≠ target` of `target` lands on an ancestor of `target`, then `ghost` from `anchor` ends at
    `target` or a descendant of `target`. -/
theorem ghost_passes {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hpre : Block.Preceq anchor target)
    (hpath : ∀ C : Block V, Block.Preceq anchor C → C ≠ anchor → Block.Preceq C target →
      C ∈ tree)
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    Block.Preceq target (Protocol.ghost anchor tree score eligible) :=
  ghost_walk_passes hstep tree.card anchor (Block.preceq_self _) hpre
    (path_card anchor target tree hpre hpath)

omit [Fintype V] in
/-- If `A` and `B` are compatible, `ghost` from `A` reaches `B` or a descendant of `B` whenever
    `A ⪯ B`, and neither `A` nor any block of `tree` is a proper descendant of `B`, then `ghost`
    from `A` is `B`. -/
theorem ghost_eq_of_compatible_anchor_and_terminal
    {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {A B : Block V}
    (hcompat : Block.compatible A B = true)
    (hforward : Block.Preceq A B →
      Block.Preceq B (Protocol.ghost A tree score eligible))
    (hanchorTerminal : Block.Preceq B A → A = B)
    (htreeTerminal : ∀ X ∈ tree, Block.Preceq B X → X = B) :
    Protocol.ghost A tree score eligible = B := by
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hAB | hBA
  · have hBhead := hforward hAB
    rcases Proofs.Records.ghost_mem A tree score eligible with hhead | hmem
    · rw [hhead] at hBhead ⊢
      exact Block.preceq_antisymm hAB hBhead
    · exact htreeTerminal _ hmem hBhead
  · have hBhead := Block.preceq_trans hBA
      (ghost_preceq A tree score eligible)
    rcases Proofs.Records.ghost_mem A tree score eligible with hhead | hmem
    · rw [hhead, hanchorTerminal hBA]
    · exact htreeTerminal _ hmem hBhead

/-! ## The Goldfish eligibility test -/

/-- `goldfish_eligible` holds of `B` exactly when `B`'s parent's chain-state height is less than
    `h_max - 1`, or `B` passes the majority test, or `B` is of the current slot. -/
theorem goldfish_eligible_iff (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (B : Block V) :
    Protocol.goldfish_eligible E σ h_max T cur votes support_votes s B = true ↔
      ((σ B.parent).h < h_max - 1 ∨
        Protocol.voters_count E votes s <
          2 * Protocol.goldfish_score E T votes support_votes s B ∨
        B.slot = cur) := by
  simp only [Protocol.goldfish_eligible, Bool.or_eq_true, decide_eq_true_eq, or_assoc]

/-- A block of the current slot is `goldfish_eligible`. -/
theorem goldfish_eligible_current (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    {B : Block V} (hB : B.slot = cur) :
    Protocol.goldfish_eligible E σ h_max T cur votes support_votes s B = true := by
  rw [goldfish_eligible_iff]
  exact Or.inr (Or.inr hB)


/-! ## The walk reaches a block an honest cone supports -/


/-- Under `ConeSupport` for the descendants of `B` on a valid vote set, if `A ⪯ B` and the path from
    `A` to `B` is in `tree`, the confirmation walk from `A` ends at `B` or a descendant of `B`. -/
theorem ghost_passes_cone (E : Env V) (T tree : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    {A B : Block V}
    (hsup : ConeSupport E T votes support late s Hon (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E s late)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B (Protocol.ghost A tree (Protocol.goldfish_score E T votes support s)
      (fun C => decide (Protocol.voters_count E late s <
        2 * Protocol.goldfish_score E T votes support s C))) := by
  refine ghost_passes hAB hpath ?_
  intro Hd hAHd hHdB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHdB hne
  have hAC : Block.Preceq A C := Block.preceq_trans hAHd (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = Hd.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ Hd.depth := Block.preceq_depth_le hAHd
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hUnder : Under (fun X => Block.Preceq B X) C := by
    intro X hX
    exact Block.preceq_trans hCB hX
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_unique ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    exact ⟨hCmem, hCpar, by
      simp only [decide_eq_true_eq]
      exact hsup.eligible hvalid hUnder⟩
  · intro D hD
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    obtain ⟨-, hDpar, hDel⟩ := hD
    simp only [decide_eq_true_eq] at hDel
    have hDB : Block.preceq D B = true := by
      by_contra hcon
      have hfalse : Block.preceq D B = false := by simpa using hcon
      have hdep : D.depth ≤ B.depth := by
        have h1 : D.depth = Hd.depth + 1 := depth_of_parent? hDpar
        have h2 : Hd.depth < B.depth := by
          have h3 := Block.preceq_depth_le hHdB
          rcases Nat.lt_or_ge Hd.depth B.depth with h | h
          · exact h
          · exact absurd (Block.preceq_eq_of_depth_le hHdB h) hne
        omega
      exact hsup.not_eligible hvalid (off_of_depth hfalse hdep) hDel
    exact child_towards_unique hCpar hDpar hCB hDB


/-! ## The composed head -/


/-- The candidate tree a voter walks: the filtered block tree of the store's FG view. -/
def voter_candidate_tree (E : Env V) (st : Protocol.HealingStore V) :
    Finset (Block V) :=
  Protocol.get_filtered_block_tree_from st.toFG
    (Protocol.voter_processed_block_tree E st.toFG.toSG.toGoldfishStore st.s)


/-- Under any grade contract, the head in `tree` is the Goldfish fork choice from the contract's
    anchor `get_sg_root_with` at the store's round. -/
theorem get_head_in_tree_split_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.HealingStore V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) :
    Protocol.get_head_in_tree_with_layer contract E hc st tree votes support_votes k =
      Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s
        (Protocol.get_sg_root_with contract E hc st (hc.round_of st.s))
        tree votes support_votes k :=
  rfl

/-- `voter_candidate_tree` of a store is `Protocol.voter_filtered_block_tree` at the store's slot. -/
theorem voter_candidate_tree_eq_protocol_voter_filtered_block_tree (E : Env V)
    (st : Protocol.Store V) :
    voter_candidate_tree E st.toHealing =
      Protocol.voter_filtered_block_tree E st st.s :=
  rfl


/-! ## The vote read at one honest store -/


/-- At `v`'s slot-`s` vote read, the proposal `B` extends the head `H`, is a fresh leaf added to the
    tree `tree₀`, and is the voter's head. -/
structure NamedVoteStoreExtends (S : Setup V) (ρ : Run V) (v : V) (s : Slot)
    (tree₀ : Finset (Block V)) (H : Block V) (B : NamedBlock V) : Prop where
  /-- The proposal is of the read's current slot. -/
  cur : B.slot = (voteDutyRead S ρ v s).st.core.s
  /-- The proposal's parent is `H`. -/
  parent : B.erase.parent? = some H
  /-- The voter's candidate tree is `tree₀` with the proposal added. -/
  tree : voterCandidateTreeAt S ρ v s = insert B.erase tree₀
  /-- The proposal is not in `tree₀`. -/
  fresh : B.erase ∉ tree₀
  /-- No block of `tree₀` has the proposal as parent. -/
  leaf : ∀ C ∈ tree₀, C.parent? ≠ some B.erase
  /-- The voter's head is the proposal. -/
  head : voterHeadAt S ρ v s = B.erase


/-! ## Honest heads stay in the cone -/

/-- Under `ConeSupport` for the descendants of `B` on a valid vote set, if `A ⪯ B` and the path from
    `A` to `B` is in `tree`, the Goldfish fork choice from `A` is `B` or a descendant of `B`. -/
theorem goldfish_passes_cone (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V))
    (k : Slot) (Hon : Finset V) {A B : Block V}
    (hsup : ConeSupport E T votes support votes k Hon (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E k votes)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support k) := by
  rw [Protocol.goldfish_fork_choice]
  refine ghost_passes hAB hpath ?_
  intro Hd hAHd hHdB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHdB hne
  have hAC : Block.Preceq A C := Block.preceq_trans hAHd (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = Hd.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ Hd.depth := Block.preceq_depth_le hAHd
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hUnder : Under (fun X => Block.Preceq B X) C :=
    fun X hX => Block.preceq_trans hCB hX
  have hHdlt : Hd.depth < B.depth := by
    rcases Nat.lt_or_ge Hd.depth B.depth with h | h
    · exact h
    · exact absurd (Block.preceq_eq_of_depth_le hHdB h) hne
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_dominates ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    refine ⟨hCmem, hCpar, ?_⟩
    rw [goldfish_eligible_iff]
    exact Or.inr (Or.inl (hsup.eligible hvalid hUnder))
  · intro D hD hDC
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    have hDpar := hD.2.1
    have hDB : Block.preceq D B = false := by
      rw [← Bool.not_eq_true]
      intro hcon
      exact hDC (child_towards_unique hCpar hDpar hCB hcon)
    have hdep : D.depth ≤ B.depth := by
      have h1 : D.depth = Hd.depth + 1 := depth_of_parent? hDpar
      omega
    exact hsup.score_lt hvalid hUnder (off_of_depth hDB hdep)


omit [Fintype V] in
/-- Adding a block with parent `H` leaves the children of every other block `X ≠ H` unchanged. -/
theorem ghost_children_insert_of_ne {tree : Finset (Block V)} {eligible : Block V → Bool}
    {B H X : Block V} (hpar : B.parent? = some H) (hne : X ≠ H) :
    Protocol.ghost_children (insert B tree) eligible X =
      Protocol.ghost_children tree eligible X := by
  rw [Protocol.ghost_children, Protocol.ghost_children, Finset.filter_insert, if_neg]
  rintro ⟨hp, -⟩
  rw [hpar, Option.some.injEq] at hp
  exact hne hp.symm

omit [Fintype V] in

/-- If `H` had no eligible child and the added eligible block `B` has parent `H`, then `B` is `H`'s
    only eligible child. -/
theorem ghost_children_insert_self {tree : Finset (Block V)} {eligible : Block V → Bool}
    {B H : Block V} (hpar : B.parent? = some H) (helig : eligible B = true)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false) :
    Protocol.ghost_children (insert B tree) eligible H = {B} := by
  rw [Protocol.ghost_children, Finset.filter_insert, if_pos ⟨hpar, helig⟩]
  have hempty : tree.filter (fun C => C.parent? = some H ∧ eligible C = true) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    rintro C hC ⟨h1, h2⟩
    rw [hstop C hC h1] at h2
    simp at h2
  rw [hempty]
  simp

omit [Fintype V] in
/-- If `H` had no eligible child and the added eligible block `B` has parent `H`, the step from `H`
    goes to `B`. -/
theorem ghost_step_insert_self {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B H : Block V} (hpar : B.parent? = some H)
    (helig : eligible B = true)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false) :
    Protocol.ghost_step (insert B tree) score eligible H = some B := by
  rw [Protocol.ghost_step, ghost_children_insert_self hpar helig hstop]
  exact argmax?_eq_some_of_unique (by simp) (by simp)

omit [Fintype V] in

/-- If no block of `tree` has parent `B`, the step from the added block `B` stops. -/
theorem ghost_step_insert_leaf {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B H : Block V} (hpar : B.parent? = some H)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B) :
    Protocol.ghost_step (insert B tree) score eligible B = none := by
  refine ghost_step_none ?_
  intro C hC hCB
  rcases Finset.mem_insert.mp hC with hEq | hmem
  · exfalso
    rw [hEq, hpar, Option.some.injEq] at hCB
    have h1 := depth_of_parent? hpar
    rw [hCB] at h1
    omega
  · exact absurd hCB (hfresh C hmem)

omit [Fintype V] in
/-- A walk that ends at `H` over `tree` ends at `B` over `insert B tree` with one more unit of fuel,
    when `B` is a fresh eligible leaf child of `H` and `H` had no eligible child. -/
theorem ghost_walk_insert {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {B H : Block V}
    (hpar : B.parent? = some H) (helig : eligible B = true)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B) :
    ∀ (n : Nat) (X : Block V), Protocol.ghost_walk tree score eligible n X = H →
      Protocol.ghost_walk (insert B tree) score eligible (n + 1) X = B := by
  have hstepH : Protocol.ghost_step (insert B tree) score eligible H = some B :=
    ghost_step_insert_self hpar helig hstop
  have hstepB : Protocol.ghost_step (insert B tree) score eligible B = none :=
    ghost_step_insert_leaf hpar hfresh
  intro n
  induction n with
  | zero =>
      intro X hres
      simp only [Protocol.ghost_walk] at hres
      subst hres
      simp only [Protocol.ghost_walk, hstepH]
  | succ n ih =>
      intro X hres
      rw [Protocol.ghost_walk] at hres
      cases hs : Protocol.ghost_step tree score eligible X with
      | none =>
          rw [hs] at hres
          subst hres
          simp only [Protocol.ghost_walk, hstepH, hstepB]
      | some C =>
          rw [hs] at hres
          have hXH : X ≠ H := by
            intro hEq
            rw [hEq] at hs
            rw [ghost_step_none hstop] at hs
            exact absurd hs (by simp)
          have hs' : Protocol.ghost_step (insert B tree) score eligible X = some C := by
            rw [Protocol.ghost_step, ghost_children_insert_of_ne hpar hXH, ← Protocol.ghost_step]
            exact hs
          rw [Protocol.ghost_walk, hs']
          exact ih C hres

omit [Fintype V] in
/-- If `ghost` from `A` over `tree` is `H`, then over `insert B tree` it is `B`, when `B ∉ tree` is
    an eligible leaf child of `H` and `H` had no eligible child. -/
theorem ghost_insert_eq {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {A B H : Block V}
    (hpar : B.parent? = some H) (helig : eligible B = true)
    (hnotin : B ∉ tree)
    (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false)
    (hfresh : ∀ C ∈ tree, C.parent? ≠ some B)
    (hwalk : Protocol.ghost A tree score eligible = H) :
    Protocol.ghost A (insert B tree) score eligible = B := by
  rw [Protocol.ghost, Finset.card_insert_of_notMem hnotin]
  exact ghost_walk_insert hpar helig hstop hfresh tree.card A hwalk


/-! ## Honest support counted against the participants -/

/-- Honest support for a cone `tgt` of targets at slot `s`, counted against the participants of the
    denominator's votes: the participants of `late` are fewer than twice the honest committee
    members, the counted votes are within the denominator's votes, the support votes are within the
    raw votes, no honest committee member equivocates, and each casts a support vote naming a block
    `tgt` admits. -/
structure ConeSupportCount (E : Env V) (T : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    (tgt : Block V → Prop) : Prop where
  /-- `|participants(late)| < 2·|K_s ∩ Hon|`. -/
  count : Protocol.voters_count E late s < 2 * ((E.committee s) ∩ Hon).card
  /-- The counted votes are within the denominator's votes. -/
  counted : votes ⊆ late
  /-- The support votes are within the raw votes. -/
  sub : support ⊆ votes
  /-- No honest committee member equivocates in the raw votes. -/
  no_equiv : ∀ x ∈ E.committee s, x ∈ Hon → Protocol.equivocates votes x = false
  /-- Every honest committee member has a slot-`s` support vote whose head resolves in `T` to a
      block of its slot or earlier that `tgt` admits. -/
  vote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧
    ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X

/-- If every vote of `votes` names a member of `X`, the participants of `votes` number at most
    `X.card`. -/
theorem voters_count_le_card_of_valIndex (E : Env V) (votes : Finset (GoldfishVote V)) (s : Slot)
    (X : Finset V) (h : ∀ u ∈ votes, u.val_index ∈ X) :
    Protocol.voters_count E votes s ≤ X.card := by
  simp only [Protocol.voters_count, Protocol.raw_voters_count]
  refine Finset.card_le_card ?_
  intro w hw
  simp only [Protocol.raw_participants, Finset.mem_filter, Finset.mem_univ, true_and] at hw
  rw [Protocol.participates, decide_eq_true_eq] at hw
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hw
  rw [Protocol.votes_by, Finset.mem_filter] at hu
  rw [← hu.2]
  exact h u hu.1

namespace ConeSupportCount

variable {E : Env V} {T : Finset (Block V)}
  {votes support late : Finset (GoldfishVote V)}
  {s : Slot} {Hon : Finset V} {tgt : Block V → Prop}

/-- Every honest committee member supports every block `C` the cone lies under. -/
theorem subset_supporters (h : ConeSupportCount E T votes support late s Hon tgt)
    {C : Block V} (hC : Under tgt C) :
    (E.committee s) ∩ Hon ⊆ Protocol.goldfishSupporters E T votes support s C := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, hslot, X, hfind, hXslot, htgt⟩ := h.vote x hx.1 hx.2
  rw [mem_supporters_iff]
  refine ⟨h.no_equiv x hx.1 hx.2, u, ?_, hslot,
    targets_under_iff.mpr ⟨X, hfind, hXslot, hC X htgt⟩⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨hu, hval⟩

/-- Every honest committee member is a participant of the denominator's votes. -/
theorem subset_participants (h : ConeSupportCount E T votes support late s Hon tgt) :
    (E.committee s) ∩ Hon ⊆ Protocol.participants E late s := by
  intro x hx
  rw [Finset.mem_inter] at hx
  obtain ⟨u, hu, hval, -, -⟩ := h.vote x hx.1 hx.2
  simp only [Protocol.participants, Protocol.raw_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [Protocol.participates, decide_eq_true_eq]
  refine Finset.card_pos.mpr ⟨u, ?_⟩
  rw [Protocol.votes_by, Finset.mem_filter]
  exact ⟨h.counted (h.sub hu), hval⟩

/-- No honest committee member supports a block `D` off the cone. -/
theorem not_mem_supporters (h : ConeSupportCount E T votes support late s Hon tgt)
    {D : Block V}
    (hD : Off tgt D) {x : V} (hx : x ∈ E.committee s) (hxH : x ∈ Hon) :
    x ∉ Protocol.goldfishSupporters E T votes support s D := by
  intro hmem
  rw [mem_supporters_iff] at hmem
  obtain ⟨-, u', hu', -, htar⟩ := hmem
  obtain ⟨u, hu, hval, -, X, hfind, hXslot, htgt⟩ := h.vote x hx hxH
  have hcard : (Protocol.votes_by votes x).card ≤ 1 := by
    have hne := h.no_equiv x hx hxH
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hne
    omega
  have huin : u ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter]
    exact ⟨h.sub hu, hval⟩
  have hu'raw : u' ∈ Protocol.votes_by votes x := by
    rw [Protocol.votes_by, Finset.mem_filter] at hu' ⊢
    exact ⟨h.sub hu'.1, hu'.2⟩
  have hsame : u' = u := Finset.card_le_one.mp hcard u' hu'raw u huin
  obtain ⟨Y, hfindY, hpre⟩ := targets_under_iff.mp htar
  rw [hsame, hfind] at hfindY
  have hYX : Y = X := by simpa using hfindY.symm
  subst hYX
  exact absurd hpre.2 (by rw [hD Y htgt]; simp)

/-- The score of a block `D` off the cone plus the number of honest committee members is at most the
    number of participants. -/
theorem score_add_le (h : ConeSupportCount E T votes support late s Hon tgt) {D : Block V}
    (hD : Off tgt D) :
    Protocol.goldfish_score E T votes support s D + ((E.committee s) ∩ Hon).card ≤
      Protocol.voters_count E late s := by
  have hdisj1 : Disjoint (Protocol.equivocators E votes s)
      (Protocol.goldfishSupporters E T votes support s D) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Protocol.equivocators, Protocol.raw_equivocators, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rw [mem_supporters_iff] at hx'
    rw [hx'.1] at hx
    simp at hx
  have hdisj2 : Disjoint ((Protocol.equivocators E votes s) ∪
      (Protocol.goldfishSupporters E T votes support s D)) ((E.committee s) ∩ Hon) := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_union]
    rintro (hx' | hx')
    · simp only [Protocol.equivocators, Protocol.raw_equivocators,
        Finset.mem_filter, Finset.mem_univ, true_and] at hx'
      rw [h.no_equiv x hx.1 hx.2] at hx'
      simp at hx'
    · exact h.not_mem_supporters hD hx.1 hx.2 hx'
  have hsub : ((Protocol.equivocators E votes s) ∪
      (Protocol.goldfishSupporters E T votes support s D)) ∪ ((E.committee s) ∩ Hon) ⊆
      Protocol.participants E late s := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) h.subset_participants
    · exact equivocators_subset_participants E h.counted s
    · exact supporters_subset_participants E T (subset_trans h.sub h.counted) s D
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1] at hcard
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.equivocators, Protocol.goldfishSupporters, Protocol.voters_count,
    Protocol.raw_voters_count, Protocol.participants] at hcard ⊢
  omega


/-- A block `C` the cone lies under scores at least the number of honest committee members. -/
theorem le_score (h : ConeSupportCount E T votes support late s Hon tgt) {C : Block V}
    (hC : Under tgt C) :
    ((E.committee s) ∩ Hon).card ≤ Protocol.goldfish_score E T votes support s C := by
  have hle := Finset.card_le_card (h.subset_supporters hC)
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score,
    Protocol.goldfishSupporters] at hle ⊢
  omega

/-- A block `C` the cone lies under passes the majority test. -/
theorem eligible (h : ConeSupportCount E T votes support late s Hon tgt) {C : Block V}
    (hC : Under tgt C) :
    Protocol.voters_count E late s <
      2 * Protocol.goldfish_score E T votes support s C := by
  have h1 := h.count
  have h2 := h.le_score hC
  omega

/-- A block `D` off the cone fails the majority test. -/
theorem not_eligible (h : ConeSupportCount E T votes support late s Hon tgt) {D : Block V}
    (hD : Off tgt D) :
    ¬ Protocol.voters_count E late s <
      2 * Protocol.goldfish_score E T votes support s D := by
  have h1 := h.count
  have h2 := h.score_add_le hD
  omega

/-- A block `D` off the cone scores less than every block `C` the cone lies
    under. -/
theorem score_lt (h : ConeSupportCount E T votes support late s Hon tgt) {C D : Block V}
    (hC : Under tgt C) (hD : Off tgt D) :
    Protocol.goldfish_score E T votes support s D <
      Protocol.goldfish_score E T votes support s C := by
  have h1 := h.count
  have h2 := h.score_add_le hD
  have h3 := h.le_score hC
  omega

end ConeSupportCount


/-- Under `ConeSupportCount` for the descendants of `B`, if `A ⪯ B` and the path from
    `A` to `B` is in `tree`, the confirmation walk from `A` ends at `B` or a descendant of `B`. -/
theorem ghost_passes_cone_count (E : Env V) (T tree : Finset (Block V))
    (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V)
    {A B : Block V}
    (hsup : ConeSupportCount E T votes support late s Hon (fun X => Block.Preceq B X))
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B (Protocol.ghost A tree (Protocol.goldfish_score E T votes support s)
      (fun C => decide (Protocol.voters_count E late s <
        2 * Protocol.goldfish_score E T votes support s C))) := by
  refine ghost_passes hAB hpath ?_
  intro Hd hAHd hHdB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHdB hne
  have hAC : Block.Preceq A C := Block.preceq_trans hAHd (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = Hd.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ Hd.depth := Block.preceq_depth_le hAHd
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hUnder : Under (fun X => Block.Preceq B X) C := by
    intro X hX
    exact Block.preceq_trans hCB hX
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_unique ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    exact ⟨hCmem, hCpar, by
      simp only [decide_eq_true_eq]
      exact hsup.eligible hUnder⟩
  · intro D hD
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    obtain ⟨-, hDpar, hDel⟩ := hD
    simp only [decide_eq_true_eq] at hDel
    have hDB : Block.preceq D B = true := by
      by_contra hcon
      have hfalse : Block.preceq D B = false := by simpa using hcon
      have hdep : D.depth ≤ B.depth := by
        have h1 : D.depth = Hd.depth + 1 := depth_of_parent? hDpar
        have h2 : Hd.depth < B.depth := by
          have h3 := Block.preceq_depth_le hHdB
          rcases Nat.lt_or_ge Hd.depth B.depth with h | h
          · exact h
          · exact absurd (Block.preceq_eq_of_depth_le hHdB h) hne
        omega
      exact hsup.not_eligible (off_of_depth hfalse hdep) hDel
    exact child_towards_unique hCpar hDpar hCB hDB


/-- Under `ConeSupportCount` for the descendants of `B`, if `A ⪯ B` and the path from
    `A` to `B` is in `tree`, the Goldfish fork choice from `A` is `B` or a descendant of `B`. -/
theorem goldfish_passes_cone_count (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V))
    (k : Slot) (Hon : Finset V) {A B : Block V}
    (hsup : ConeSupportCount E T votes support votes k Hon (fun X => Block.Preceq B X))
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) :
    Block.Preceq B
      (Protocol.goldfish_fork_choice E σ h_max T cur A tree votes support k) := by
  rw [Protocol.goldfish_fork_choice]
  refine ghost_passes hAB hpath ?_
  intro Hd hAHd hHdB hne
  obtain ⟨C, hCpar, hCB⟩ := exists_child_towards B hHdB hne
  have hAC : Block.Preceq A C := Block.preceq_trans hAHd (preceq_of_parent? hCpar)
  have hCne : C ≠ A := by
    intro hEq
    have h1 : C.depth = Hd.depth + 1 := depth_of_parent? hCpar
    have h2 : A.depth ≤ Hd.depth := Block.preceq_depth_le hAHd
    rw [hEq] at h1
    omega
  have hCmem : C ∈ tree := hpath C hAC hCne hCB
  have hUnder : Under (fun X => Block.Preceq B X) C :=
    fun X hX => Block.preceq_trans hCB hX
  have hHdlt : Hd.depth < B.depth := by
    rcases Nat.lt_or_ge Hd.depth B.depth with h | h
    · exact h
    · exact absurd (Block.preceq_eq_of_depth_le hHdB h) hne
  refine ⟨C, ?_, hCB⟩
  rw [Protocol.ghost_step]
  refine argmax?_eq_some_of_dominates ?_ ?_
  · rw [Protocol.ghost_children, Finset.mem_filter]
    refine ⟨hCmem, hCpar, ?_⟩
    rw [goldfish_eligible_iff]
    exact Or.inr (Or.inl (hsup.eligible hUnder))
  · intro D hD hDC
    rw [Protocol.ghost_children, Finset.mem_filter] at hD
    have hDpar := hD.2.1
    have hDB : Block.preceq D B = false := by
      rw [← Bool.not_eq_true]
      intro hcon
      exact hDC (child_towards_unique hCpar hDpar hCB hcon)
    have hdep : D.depth ≤ B.depth := by
      have h1 : D.depth = Hd.depth + 1 := depth_of_parent? hDpar
      omega
    exact hsup.score_lt hUnder (off_of_depth hDB hdep)


end Optimistic
end Proofs
end DecoupledConsensusModel

end
