module
public import GoldilocksCorrectness.Proofs.Routines.Frame
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Routines.NoRaise
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
import all Goldilocks.AC.Confirmation
import all Goldilocks.AC.State
import all Goldilocks.Config
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# What the confirmation update saves, from the votes of its pool

The theorems about `update_confirmation` that read the votes it counts and the supporters
`EarlySupporterOf` of a block: `update_confirmation_saved_mem`, `update_confirmation_saves`,
`update_confirmation_supporter`, `update_confirmation_saves_of_supporters`; and
`update_confirmation_ok`: the update raises no error.

They read the routine and an AC state alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, a saved confirmation is the frame's finalized block or in its tree.** The
confirmation the update of slot `s ≥ 1` saves for slot `s − 1`, when it saves one, is `Φ.F` or a
block of `Φ.tree`: it is the end of the walk from `Φ.F` through `Φ.tree`.

The variables:
- `C`, `P`: the parameters and the values; `A`, `A'`: the AC state before and after the update;
  `Φ`: the frame; `t`: the time; `s`: the slot of the update; `C'`: the saved block. -/
theorem update_confirmation_saved_mem (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot)
    -- the update is of a slot after slot `0`
    (hs : 1 ≤ s)
    -- the update answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A') (C' : Block V)
    -- `A'` saves `C'` as the confirmation of slot `s − 1`
    (hC' : A'.saved_confirmation (s - 1) = some C') :
    C' = Φ.F ∨ C' ∈ Φ.tree := by
  obtain ⟨early, late, H, b, -, -, hH, -, hsaved⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_walk C P A A' Φ t s hs hUpdate
  rw [hsaved] at hC'
  split at hC'
  · cases hC'
    exact GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq hH
  · cases hC'

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf RootsNameBlocksIn VotesOnceFor)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The confirmation update saves a block when a voter majority supports the frame's finalized
block.** The confirmation update of slot `s ≥ 1` saves some block as the confirmation of slot
`s − 1` when the roots of `Φ.tree` name its blocks, every member of `Hs` has exactly one
slot-`(s − 1)` vote in `A`'s pool, early, with its head a block of `Φ.tree` (so `Φ.F` or a
descendant of `Φ.F`), every vote of the pool has the slot `s − 1`, and fewer than twice `Hs`
validators have a vote in the pool.

Why: the walk from `Φ.F` steps only onto blocks that pass the eligibility test, so its end passes
it, or is `Φ.F` itself; `Φ.F`'s score counts every member of `Hs` (each a support vote, its
validator's only one, as in Lemma 77), and the late voters are fewer than twice `Hs`.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `A`: the AC state before the update;
  `A'`: the AC state after it; `Φ`: the frame; `t`: the time of the update; `s`: the slot of the
  update; `Hs`: the validators voting early for `Φ.F`'s chain. -/
theorem update_confirmation_saves (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hHs : ∀ v ∈ Hs, EarlySupporterOf C A Φ (s - 1) Φ.F v)
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    ∃ C' : Block V, A'.saved_confirmation (s - 1) = some C' := by
  obtain ⟨early, late, H, b, hEarly, hLate, hH, hb, hsaved⟩ :=
    update_confirmation_walk C P A A' Φ t s hs hUpdate
  -- the early votes are late votes, and both are votes of the pool
  have hEarlyLate : early ⊆ late := by
    intro vote hv
    obtain ⟨hp, x, hτ, hx⟩ := (hEarly vote).1 hv
    obtain ⟨τ, hts, hτx⟩ := tau_eq_some_stamp hτ
    refine (hLate vote).2 ⟨hp, τ, hts, ?_⟩
    have hΔ : (0 : Int) < C.Δ := C.Δ_pos
    have hlt : C.t_ (s - 1) + 2 * C.Δ < C.t_ (s - 1) + 6 * C.Δ :=
      Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
    have hc : ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp) <
        ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp) := WithBot.coe_lt_coe.2 hlt
    exact lt_of_le_of_lt hτx (lt_trans hx hc)
  have hLatePool : late ⊆ A.pool (s - 1) := fun vote hv => ((hLate vote).1 hv).1
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late :=
    fun vote hv => hEarlyLate (Finset.mem_filter.1 hv).1
  have hSupPool : {vote ∈ early | no_second_vote_in late vote = true} ⊆ A.pool (s - 1) :=
    fun vote hv => hLatePool (hSupLate hv)
  -- each member of `Hs` has one support vote, for `Φ.F`'s chain
  have hMem : ∀ v ∈ Hs, VotesOnceFor Φ {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) Φ.F v := by
    intro v hv
    obtain ⟨vote, hvote, hval, hhead, ⟨x, hτ, hx⟩, hu⟩ := hHs v hv
    obtain ⟨y, hy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hx
    cases hy
    have hE : vote ∈ early := (hEarly vote).2 ⟨hvote, x, hτ, hlt⟩
    have hN : no_second_vote_in late vote = true := by
      simp only [no_second_vote_in, decide_eq_true_eq]
      intro u hu'
      by_cases huv : u.val_index = vote.val_index
      · exact Or.inl (hu u (hLatePool hu') (huv.trans hval))
      · exact Or.inr huv
    exact ⟨vote, Finset.mem_filter.2 ⟨hE, hN⟩, hval, hSlot vote hvote, hhead,
      fun vote' hv' hval' => hu vote' (hSupPool hv') hval'⟩
  -- the counting
  have hPartLate : participants late ⊆ participants (A.pool (s - 1)) := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hLatePool hvote, hval⟩
  have hNle : voters_count late ≤ voters_count (A.pool (s - 1)) := Finset.card_le_card hPartLate
  have hSupF : Hs ⊆ supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) Φ.F :=
    fun v hv => mem_supportersOf_of_votesOnceFor (hMem v hv) (ancestorEq_refl _)
  have hcard := Finset.card_le_card hSupF
  -- the end of the walk passes the test
  have hbt : b = true := by
    rcases ghost_spec hH with hHF | ⟨-, hel⟩
    · rw [hHF, goldfish_score_eq_ok hRoots] at hb
      simp only [dre_bind_ok] at hb
      have hb' : (Except.ok (decide (voters_count late < 2 * ((equivocators
          {vote ∈ early | no_second_vote_in late vote = true}).card + (supportersOf Φ
          {vote ∈ early | no_second_vote_in late vote = true}
          {vote ∈ early | no_second_vote_in late vote = true} (s - 1) Φ.F).card))) : DRE Bool) =
          Except.ok b := hb
      injection hb' with hb''
      rw [← hb'']
      exact decide_eq_true (by omega)
    · have h := hel.symm.trans hb
      injection h with h'
      exact h'.symm
  rw [hbt] at hsaved
  exact ⟨H, by rw [hsaved]; rfl⟩

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **A saved confirmation is supported by a member of every voter majority.** When the
confirmation update of slot `s' + 1` saves `X` as the confirmation of slot `s'`, the roots of
`Φ.tree` name its blocks, every member `u` of `Hs` has exactly one slot-`s'` vote `vote u` in `A`'s
pool, stamped strictly before `C.t_ s' + 6Δ`, and fewer than twice `Hs` validators have a vote in
the pool, then some member `u` of `Hs` has its vote's head the root of a block of `Φ.tree` that is
`X` or a descendant of `X`.

Why: `X` passed the test `voters_count < 2 · score X`. The members of `Hs` are counted voters, none
an equivocator of the support votes (one vote each); were none a supporter of `X`, the equivocators
and the supporters of `X` (disjoint) would be among the other counted voters, and
`voters_count < 2 · (voters_count − |Hs|)` would give `2 |Hs| < voters_count`, against the
hypothesis.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `A`: the AC state before the update;
  `A'`: the AC state after it; `Φ`: the frame; `t`: the time of the update; `s'`: the slot of the
  votes; `Hs`: the voters; `vote`: each voter's vote; `X`: the confirmation. -/
theorem update_confirmation_supporter (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s' : Slot) (Hs : Finset V) (vote : V → GoldfishVote V)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hHs : ∀ u ∈ Hs, vote u ∈ A.pool s' ∧ (vote u).val_index = u ∧
      (∃ τ : Stamp, A.timestamp_vote (vote u) = some τ ∧
        τ < ((C.t_ s' + 6 * C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ A.pool s', vote'.val_index = u → vote' = vote u)
    (hVoters : voters_count (A.pool s') < 2 * Hs.card)
    (hUpdate : update_confirmation C P A Φ t (s' + 1) = .ok A') (X : Block V)
    (hX : A'.saved_confirmation s' = some X) :
    ∃ u ∈ Hs, ∃ H ∈ Φ.tree, H.root = (vote u).head ∧ X.AncestorEq H := by
  obtain ⟨early, late, H, b, hEarly, hLate, -, hb, hsaved⟩ :=
    GoldilocksCorrectness.Proofs.Routines.update_confirmation_walk C P A A' Φ t (s' + 1)
      (Nat.le_add_left 1 s') hUpdate
  simp only [Nat.add_sub_cancel] at hEarly hLate hb hsaved
  rw [hX] at hsaved
  cases b with
  | false => simp at hsaved
  | true =>
  simp only [if_true, Option.some.injEq] at hsaved
  subst hsaved
  -- the early votes are late votes
  have hEarlyLate : early ⊆ late := by
    intro vt hv
    obtain ⟨hp, y, hτ, hy⟩ := (hEarly vt).1 hv
    obtain ⟨τ, hts, hτy⟩ := GoldilocksCorrectness.Proofs.Routines.tau_eq_some_stamp hτ
    refine (hLate vt).2 ⟨hp, τ, hts, ?_⟩
    have hΔ : (0 : Int) < C.Δ := C.Δ_pos
    have hlt : C.t_ s' + 2 * C.Δ < C.t_ s' + 6 * C.Δ :=
      Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
    have hc : ((C.t_ s' + 2 * C.Δ : Time) : Stamp) <
        ((C.t_ s' + 6 * C.Δ : Time) : Stamp) := WithBot.coe_lt_coe.2 hlt
    exact lt_of_le_of_lt hτy (lt_trans hy hc)
  have hLatePool : late ⊆ A.pool s' := fun vt hv => ((hLate vt).1 hv).1
  set sv := {vt ∈ early | no_second_vote_in late vt = true} with hsv
  have hsvPool : sv ⊆ A.pool s' := fun vt hv => hLatePool (hEarlyLate (Finset.mem_filter.1 hv).1)
  have hsvLate : sv ⊆ late := fun vt hv => hEarlyLate (Finset.mem_filter.1 hv).1
  -- the test
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_score_eq_ok hRoots] at hb
  simp only [GoldilocksCorrectness.Proofs.Routines.dre_bind_ok] at hb
  have hb' : (Except.ok (decide (voters_count late < 2 * ((equivocators sv).card +
      (GoldilocksCorrectness.Proofs.Routines.supportersOf Φ sv sv s' X).card))) : DRE Bool) =
      Except.ok true := hb
  injection hb' with hb''
  have htest := of_decide_eq_true hb''
  by_contra hno
  push Not at hno
  -- the members are counted voters
  have hPart : ∀ (u : V) (vt : GoldfishVote V), vt ∈ late → vt.val_index = u →
      u ∈ participants late :=
    fun u vt hv hvu => (GoldilocksCorrectness.Proofs.Routines.mem_participants_iff _ _).2
      ⟨vt, hv, hvu⟩
  have hHsP : Hs ⊆ participants late := by
    intro u hu
    obtain ⟨hp, hval, ⟨τ, hτ, hτlt⟩, -⟩ := hHs u hu
    exact hPart u (vote u) ((hLate _).2 ⟨hp, τ, hτ, hτlt⟩) hval
  have hEq : equivocators sv ⊆ participants late \ Hs := by
    intro u hu
    rw [GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff] at hu
    obtain ⟨vt, hvt⟩ : (votes_by sv u).Nonempty := Finset.card_pos.1 (by omega)
    have hvt' := Finset.mem_filter.1 hvt
    refine Finset.mem_sdiff.2 ⟨hPart u vt (hsvLate hvt'.1) hvt'.2, fun huH => ?_⟩
    have hle : (votes_by sv u).card ≤ 1 := by
      refine Finset.card_le_one.2 (fun a ha c hc => ?_)
      have ha' := Finset.mem_filter.1 ha
      have hc' := Finset.mem_filter.1 hc
      rw [(hHs u huH).2.2.2 a (hsvPool ha'.1) ha'.2, (hHs u huH).2.2.2 c (hsvPool hc'.1) hc'.2]
    omega
  have hSupp : GoldilocksCorrectness.Proofs.Routines.supportersOf Φ sv sv s' X ⊆
      participants late \ Hs := by
    intro u hu
    obtain ⟨vt, hvt, hval, -, -, H', hH', hr, hXH⟩ :=
      (GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff _ _ _ _ _ _).1 hu
    refine Finset.mem_sdiff.2 ⟨hPart u vt (hsvLate hvt) hval, fun huH => ?_⟩
    have hvv := (hHs u huH).2.2.2 vt (hsvPool hvt) hval
    rw [hvv] at hr
    exact hno u huH H' hH' hr hXH
  have hDisj : Disjoint (equivocators sv)
      (GoldilocksCorrectness.Proofs.Routines.supportersOf Φ sv sv s' X) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨vt, -, hval, hne, -⟩ :=
      (GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff _ _ _ _ _ _).1 hu'
    exact hne hu
  have hUnion := Finset.card_union_of_disjoint hDisj
  have hle := Finset.card_le_card (Finset.union_subset hEq hSupp)
  have hsd := Finset.card_sdiff_add_card_eq_card hHsP
  have hNpool : voters_count late ≤ voters_count (A.pool s') := by
    refine Finset.card_le_card (fun u hu => ?_)
    obtain ⟨vt, hvt, hval⟩ :=
      (GoldilocksCorrectness.Proofs.Routines.mem_participants_iff _ _).1 hu
    exact (GoldilocksCorrectness.Proofs.Routines.mem_participants_iff _ _).2
      ⟨vt, hLatePool hvt, hval⟩
  unfold voters_count at htest hNpool hVoters
  omega

end

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf RootsNameBlocksIn VotesOnceFor)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, the confirmation update saves a block.** The confirmation update of slot `s ≥ 1`
saves some confirmation of slot `s − 1` under the hypotheses of Lemma 77
(`lem77_update_confirmation_extends_voter_majority_chain`): the roots of `Φ.tree` name its blocks,
`Φ.F` is `B` or an ancestor of `B`, every member of `Hs` is an early supporter of `B`'s chain, every
vote of the pool has the slot `s − 1`, and fewer than twice `Hs` validators have a vote in the pool.

Why: the update saves the end `H` of its walk from `Φ.F` when `H` passes the eligibility test. The
walk ends at `Φ.F` or at a block it stepped onto, which passed the test; `Φ.F` passes it, since
every member of `Hs` supports it and they are more than half of the voters counted.

The variables:
- `C`: the parameters; `P`: the values; `A`, `A'`: the AC state before and after the update;
- `Φ`: the frame; `t`: the time; `s`: the slot of the update; `B`: the block; `Hs`: the
  supporters. -/
theorem update_confirmation_saves_of_supporters (C : Config) (P : Provisional V)
    (A A' : ACState V) (Φ : Frame V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn Φ.tree)
    (hF : Φ.F.AncestorEq B)
    (hHs : ∀ v ∈ Hs, EarlySupporterOf C A Φ (s - 1) B v)
    (hSlot : ∀ vote ∈ A.pool (s - 1), vote.slot = s - 1)
    (hVoters : voters_count (A.pool (s - 1)) < 2 * Hs.card)
    (hUpdate : update_confirmation C P A Φ t s = .ok A') :
    ∃ C' : Block V, A'.saved_confirmation (s - 1) = some C' := by
  obtain ⟨early, late, H, b, hEarly, hLate, hH, hb, hsaved⟩ :=
    update_confirmation_walk C P A A' Φ t s hs hUpdate
  -- the early votes are late votes, and both are votes of the pool
  have hEarlyLate : early ⊆ late := by
    intro vote hv
    obtain ⟨hp, x, hτ, hx⟩ := (hEarly vote).1 hv
    obtain ⟨τ, hts, hτx⟩ := tau_eq_some_stamp hτ
    refine (hLate vote).2 ⟨hp, τ, hts, ?_⟩
    have hΔ : (0 : Int) < C.Δ := C.Δ_pos
    -- `omega` ignores facts stated at `Time`, an `abbrev` of `Int`: the step is spelled out
    have hlt : C.t_ (s - 1) + 2 * C.Δ < C.t_ (s - 1) + 6 * C.Δ :=
      Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) hΔ) _
    have hc : ((C.t_ (s - 1) + 2 * C.Δ : Time) : Stamp) <
        ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp) := WithBot.coe_lt_coe.2 hlt
    exact lt_of_le_of_lt hτx (lt_trans hx hc)
  have hLatePool : late ⊆ A.pool (s - 1) := fun vote hv => ((hLate vote).1 hv).1
  have hSupLate : {vote ∈ early | no_second_vote_in late vote = true} ⊆ late :=
    fun vote hv => hEarlyLate (Finset.mem_filter.1 hv).1
  have hSupPool : {vote ∈ early | no_second_vote_in late vote = true} ⊆ A.pool (s - 1) :=
    fun vote hv => hLatePool (hSupLate hv)
  -- each member of `Hs` has one support vote, for `B`'s chain
  have hMem : ∀ v ∈ Hs, VotesOnceFor Φ {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} (s - 1) B v := by
    intro v hv
    obtain ⟨vote, hvote, hval, hhead, ⟨x, hτ, hx⟩, hu⟩ := hHs v hv
    obtain ⟨y, hy, hlt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hx
    cases hy
    have hE : vote ∈ early := (hEarly vote).2 ⟨hvote, x, hτ, hlt⟩
    have hN : no_second_vote_in late vote = true := by
      simp only [no_second_vote_in, decide_eq_true_eq]
      intro u hu'
      by_cases huv : u.val_index = vote.val_index
      · exact Or.inl (hu u (hLatePool hu') (huv.trans hval))
      · exact Or.inr huv
    exact ⟨vote, Finset.mem_filter.2 ⟨hE, hN⟩, hval, hSlot vote hvote, hhead,
      fun vote' hv' hval' => hu vote' (hSupPool hv') hval'⟩
  -- the counting: the support voters are late voters, and the late voters are voters of the pool
  have hPartLate : participants late ⊆ participants (A.pool (s - 1)) := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hLatePool hvote, hval⟩
  have hNle : voters_count late ≤ voters_count (A.pool (s - 1)) := Finset.card_le_card hPartLate
  have hPartSup : participants {vote ∈ early | no_second_vote_in late vote = true} ⊆
      participants late := by
    intro v hv
    obtain ⟨vote, hvote, hval⟩ := (mem_participants_iff _ _).1 hv
    exact (mem_participants_iff _ _).2 ⟨vote, hSupLate hvote, hval⟩
  have hSupLe : voters_count {vote ∈ early | no_second_vote_in late vote = true} ≤
      voters_count late := Finset.card_le_card hPartSup
  -- the walk's end is eligible: it is `Φ.F`, whose supporters are every member of `Hs`, or a
  -- block the walk stepped onto
  have hbt : b = true := by
    rcases ghost_spec hH with h | ⟨-, helig⟩
    · subst h
      rw [goldfish_score_eq_ok hRoots] at hb
      simp only [dre_bind_ok] at hb
      have hb' : decide (voters_count late < 2 * ((equivocators {vote ∈ early |
          no_second_vote_in late vote = true}).card + (supportersOf Φ {vote ∈ early |
          no_second_vote_in late vote = true} {vote ∈ early | no_second_vote_in late vote = true}
          (s - 1) Φ.F).card)) = b := by
        injection hb
      have hsub : Hs ⊆ supportersOf Φ {vote ∈ early | no_second_vote_in late vote = true}
          {vote ∈ early | no_second_vote_in late vote = true} (s - 1) Φ.F :=
        fun v hv => mem_supportersOf_of_votesOnceFor (hMem v hv) hF
      have hcard := Finset.card_le_card hsub
      rw [← hb']
      exact decide_eq_true (by omega)
    · rw [helig] at hb
      injection hb with hb
      exact hb.symm
  rw [hsaved, hbt]
  exact ⟨H, rfl⟩

end

section

open GoldilocksCorrectness.Statements.Routines (PoolStamped)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The confirmation update answers when no two blocks of the frame's tree share a root, every
vote of the pool is stamped and every block of the frame's tree is stamped.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `A`: the AC state; `Φ`: the frame;
  `t`: the time; `s`: the slot. -/
theorem update_confirmation_ok (C : Config) (P : Provisional V) (A : ACState V) {Φ : Frame V}
    (hRoots : RootsNameBlocksIn Φ.tree) (t : Time) (s : Slot) (hPool : PoolStamped A)
    -- every block of the frame's tree is stamped
    (hb : ∀ H ∈ Φ.tree, A.timestamp_block H ≠ none) :
    DREOk (update_confirmation C P A Φ t s) := by
  simp only [update_confirmation]
  refine DREOk.ite (fun _ => DREOk.pure _) (fun _ => ?_)
  -- the early votes
  refine DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun vote hvote =>
    DREOk.bind_any (tau_ok A Φ vote hRoots (pool_stamped hPool _ vote hvote) hb)
      (fun _ => DREOk.pure _))) (fun _ => ?_)
  -- the late votes
  refine DREOk.bind_any (beforeCutoff_ok _ _ _ (pool_stamped hPool _)) (fun _ => ?_)
  -- the walk from `Φ.F`
  refine DREOk.bind_any (ghost_ok _ _ _ _ (goldfish_score_ok hRoots _ _ _)
    (fun D => DREOk.bind_any (goldfish_score_ok hRoots _ _ _ D) (fun _ => DREOk.pure _)))
    (fun H => ?_)
  -- the eligibility of `H`
  refine DREOk.bind_any (DREOk.bind_any (goldfish_score_ok hRoots _ _ _ H)
    (fun _ => DREOk.pure _)) (fun _ => ?_)
  -- the writes, the lock tests and the lock entry; the first filter by `fast_test` elaborates to
  -- `filterM (fast_test …)` with no bind, the second (`… || slow_test …`) keeps its bind, so
  -- each alternative of the inner `first` closes one of them; `pure` is tried last
  repeat' first
    | refine DREOk.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREOk.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREOk.bind_any (filterM_eq_ok_of_total _ _ (fun B _ => by
        first
          | exact fast_test_ok P hRoots _ _ B
          | exact DREOk.bind_any (fast_test_ok P hRoots _ _ B) (fun _ => DREOk.pure _)))
        (fun _ => ?_)
    | exact DREOk.pure _

end

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **The fast test, as an inequality.** Over a frame whose tree has no two blocks with one root,
the fast test of `B` passes exactly when the committee of slot `s'` has at most twice `B`'s Goldfish
score: the equivocators of `support_votes` and the supporters of `B` among them.

The variables:
- `P`: the provisional parameters; `Φ`: the frame; `hRoots`: no two blocks of `Φ.tree` share a
  root; `support_votes`: the votes counted; `s'`: the slot; `B`: the block tested.

Read aloud: `B` passes the fast test exactly when the slot-`s'` committee has at most twice as many
members as `B` has equivocators plus supporters in `support_votes`.

Added by the record migration, step 1h, for the execution proofs that read
`fast_test` through its body. -/
theorem fast_test_eq_ok_true_iff (P : Provisional V) {Φ : Frame V}
    (hRoots : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn Φ.tree)
    (support_votes : Finset (GoldfishVote V)) (s' : Slot) (B : Block V) :
    fast_test P Φ support_votes s' B = .ok true ↔
      (P.committee s').card ≤ 2 * ((equivocators support_votes).card +
        (supportersOf Φ support_votes support_votes s' B).card) := by
  simp only [fast_test, goldfish_score_eq_ok hRoots, dre_bind_ok, pure, Except.pure,
    Except.ok.injEq, decide_eq_true_eq]

end

end GoldilocksCorrectness.Proofs.Routines
