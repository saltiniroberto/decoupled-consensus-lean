module
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.RevokeLocks
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# What the AC interface handlers do to an AC state

The theorems about the handlers of the AC interface, `ac_on_block`, `ac_on_tick` and `ac_to_fg`,
one handler at a time: what each keeps and adds to the pool and the stamps
(`ac_on_block_timestamp_block`, `ac_on_block_votesInv`, `ac_on_block_grows`,
`ac_on_block_new_votes`, `ac_on_block_new_slot`, `ac_on_tick_votesInv`, `ac_on_tick_grows`,
`ac_on_tick_prov`), what `ac_on_tick` puts on the wire (`ac_on_tick_sends`,
`ac_on_tick_emits_vote`), and what `ac_to_fg` answers (`ac_to_fg_head_mem`,
`ac_to_fg_source_fast`, `ac_to_fg_source_mem`).

They read the handlers and an AC state alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a block at the time `t` stamps the block with `t` and changes no other block
stamp.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `B`: the block. -/
theorem ac_on_block_timestamp_block (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (B : Block V) :
    (ac_on_block C P A t B).timestamp_block =
      Function.update A.timestamp_block B (some (t : Stamp)) := by
  simp only [ac_on_block, Id.run]
  exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
    (fun A' => A'.timestamp_block = Function.update A.timestamp_block B (some (t : Stamp))) rfl
    (fun A' vote _ hA' => by rw [on_goldfish_vote_timestamp_block]; exact hA')

omit [Fintype V] in
/-- The admission of a block at a time `t ≤ t'` keeps `VotesInv` at `t'`: it admits the block's
votes one by one.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `t'`: the bound; `B`: the block. -/
theorem ac_on_block_votesInv (C : Config) (P : Provisional V) (A : ACState V) (t t' : Time)
    (B : Block V) (h : VotesInv P A t') (ht : t ≤ t') :
    VotesInv P (ac_on_block C P A t B) t' := by
  simp only [ac_on_block, Id.run]
  exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
    (fun A' => VotesInv P A' t') h
    (fun A' vote _ hA' => on_goldfish_vote_votesInv C P A' t t' vote hA' ht)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the tick of the available chain at a time `t ≤ t'` keeps `VotesInv` at `t'`
and the block stamps: it deletes lock entries, and runs the revocation, the Goldfish vote duty
and the confirmation update, each of which does.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `t'`: the bound; `v`: the node's validator; `b`, `b'`: the two wake tests. -/
theorem ac_on_tick_votesInv (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t t' : Time) (v : V) (b b' : Bool) (h : VotesInv P A t') (ht : t ≤ t') :
    DREBPost (ac_on_tick C P A Φ t v b b')
      (fun A' => VotesInv P A' t' ∧ A'.timestamp_block = A.timestamp_block) := by
  simp only [ac_on_tick]
  repeat' first
    | exact DREBPost.pure ⟨h, rfl⟩
    | exact DREBPost.pure (by assumption)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind (DREBPost.liftM (revoke_locks_from (A₀ := A) _ _ _ _
        ⟨h, rfl⟩)) (fun _ _ => ?_)
    | refine DREBPost.bind (goldfish_vote_from (A₀ := A) _ _ _ _ _ ht
        (by first | exact ⟨h, rfl⟩ | assumption)) (fun _ _ => ?_)
    | refine DREBPost.bind (DREBPost.liftM (update_confirmation_from (A₀ := A) _ _ _ _ _
        (by first | exact ⟨h, rfl⟩ | assumption))) (fun _ _ => ?_)

end

end

section

open GoldilocksCorrectness.Statements.Routines (FinalizedAncestorJustified JustifiedInTree)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every head `ac_to_fg` answers over the frame of the FG state `S` is a block of `S.T` of which
the finalized block is an ancestor, or which is the finalized block, when the finalized and the
justified blocks are in the tree and the finalized block is the justified block or an ancestor of
it: the walk ends at its anchor or in the viable tree, and the anchor is in the viable tree or is
the fork-choice root, the justified block or the finalized block.

The variables:
- `C`: the parameters; `A`: the AC state; `S`: the FG state; `t`: the time. -/
theorem ac_to_fg_head_mem (C : Config) (A : ACState V) (S : FGState V) (t : Time)
    -- the finalized block is in the tree
    (hFT : S.F ∈ S.T) (hJT : JustifiedInTree S) (hFJ : FinalizedAncestorJustified S) :
    DREPost (ac_to_fg C A (fg_to_ac S) t)
      (fun fi => fi.head ∈ S.T ∧ S.F.AncestorEq fi.head) := by
  intro fi hfi
  have hroot : get_fc_root S ∈ S.T ∧ S.F.AncestorEq (get_fc_root S) := by
    simp only [get_fc_root, Id.run]
    split
    · exact ⟨hJT, hFJ⟩
    · exact ⟨hFT, ancestorEq_refl _⟩
  have hanchor : get_anchor A (fg_to_ac S) t = (fg_to_ac S).fc_root ∨
      get_anchor A (fg_to_ac S) t ∈ (fg_to_ac S).tree := by
    simp only [get_anchor, Id.run]
    generalize hD : Block.deepest?
      {B ∈ viable_tree (fg_to_ac S) (fg_to_ac S).tree | is_locked A (fg_to_ac S) t B} = D
    cases D with
    | none => exact Or.inl rfl
    | some B =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some]
      have hmem := GoldilocksCorrectness.Proofs.Routines.deepest?_mem hD
      exact Or.inr (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).1
  simp only [ac_to_fg] at hfi
  obtain ⟨sv, -, h1⟩ := ok_of_bind_eq_ok hfi
  obtain ⟨head, hhead, h2⟩ := ok_of_bind_eq_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  have hghost : ghost (get_anchor A (fg_to_ac S) t)
      (viable_tree (fg_to_ac S) (fg_to_ac S).tree) _ _ = .ok head := hhead
  have hfc : (fg_to_ac S).fc_root = get_fc_root S := rfl
  rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq hghost with he | hin
  · rcases hanchor with ha | ha
    · rw [he, ha, hfc]
      exact hroot
    · rw [he]
      exact (mem_fg_to_ac_tree S _).1 ha
  · exact (mem_fg_to_ac_tree S _).1 (Finset.mem_filter.mp hin).1

end

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, the duty's source is a fast block.** When `ac_to_fg C A Φ t` answers `fi` with the
source `source`, `source` is a fast block of `A`.

Why: the source is the deepest block of the fast blocks of `A` in the viable tree.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time;
- `fi`: the answer; `source`: its source.

Read aloud: the attestation duty's source is one of the fast blocks. -/
theorem ac_to_fg_source_fast {C : Config} {A : ACState V} {Φ : Frame V} {t : Time}
    {fi : FGInput V} {source : Block V}
    -- `ac_to_fg` answers `fi`
    (hfi : ac_to_fg C A Φ t = .ok fi)
    -- `fi`'s source is `source`
    (hs : fi.source = some source) :
    source ∈ A.fast_blocks := by
  simp only [ac_to_fg] at hfi
  obtain ⟨sv, -, h1⟩ := GoldilocksCorrectness.Proofs.Routines.ok_of_bind_eq_ok hfi
  obtain ⟨hd, -, h2⟩ := GoldilocksCorrectness.Proofs.Routines.ok_of_bind_eq_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  rw [← h2] at hs
  exact (Finset.mem_inter.mp (deepest?_mem hs)).1

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission at the time `t` of a block, into a pool filed by slot, keeps the pool filed by
slot, holds the pool's votes and stamps, stamps the votes it adds with `t`, and stamps the block
with `t`, changing no other block stamp.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `B`: the block. -/
theorem ac_on_block_grows (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (B : Block V) (hk : SlotKeyed A) :
    SlotKeyed (ac_on_block C P A t B) ∧ ACGrows A (ac_on_block C P A t B) ∧
      (ac_on_block C P A t B).timestamp_block =
        Function.update A.timestamp_block B (some (t : Stamp)) ∧
      ACStampsAt A (ac_on_block C P A t B) t := by
  have h : SlotKeyed (ac_on_block C P A t B) ∧ ACGrows A (ac_on_block C P A t B) ∧
      ACStampsAt A (ac_on_block C P A t B) t := by
    simp only [ac_on_block, Id.run]
    exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
      (fun A' => SlotKeyed A' ∧ ACGrows A A' ∧ ACStampsAt A A' t)
      ⟨hk, ACGrows.refl A, ACStampsAt.refl A t⟩
      (fun A' vote _ hA' =>
        have h' := on_goldfish_vote_grows C P A' t vote hA'.1
        ⟨h'.1, hA'.2.1.trans h'.2.1, hA'.2.2.trans h'.2.1 h'.2.2.2⟩)
  exact ⟨h.1, h.2.1, ac_on_block_timestamp_block C P A t B, h.2.2⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the tick of the available chain at the time `t`, from a pool filed by slot,
keeps the pool filed by slot, holds the pool's votes and stamps, keeps the block stamps, and
stamps what it adds with `t`: it deletes lock entries, and runs the revocation, the Goldfish vote
duty and the confirmation update, each of which does.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests. -/
theorem ac_on_tick_grows (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) (hk : SlotKeyed A) :
    DREBPost (ac_on_tick C P A Φ t v b b')
      (fun A' => SlotKeyed A' ∧ ACGrows A A' ∧ A'.timestamp_block = A.timestamp_block ∧
        ACStampsAt A A' t) := by
  simp only [ac_on_tick]
  repeat' first
    | exact DREBPost.pure ⟨hk, ACGrows.refl A, rfl, ACStampsAt.refl A t⟩
    | exact DREBPost.pure (by assumption)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind (DREBPost.liftM (revoke_locks_grows_from (A₀ := A) _ _ _ _
        ⟨hk, ACGrows.refl A, rfl, ACStampsAt.refl A t⟩)) (fun _ _ => ?_)
    | refine DREBPost.bind (goldfish_vote_grows_from (A₀ := A) _ _ _ _ _
        (by first | exact ⟨hk, ACGrows.refl A, rfl, ACStampsAt.refl A t⟩ | assumption))
        (fun _ _ => ?_)
    | refine DREBPost.bind (DREBPost.liftM (update_confirmation_grows_from (A₀ := A) _ _ _ _ _
        (by first | exact ⟨hk, ACGrows.refl A, rfl, ACStampsAt.refl A t⟩ | assumption)))
        (fun _ _ => ?_)

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a block adds to the pool only votes of the block's `votes`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `B`: the block. -/
theorem ac_on_block_new_votes (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (B : Block V) :
    ∀ s : Slot, ∀ vote ∈ (ac_on_block C P A t B).gf_votes s, vote ∉ A.gf_votes s →
      vote ∈ B.votes := by
  simp only [ac_on_block, Id.run]
  exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
    (fun A' => ∀ s : Slot, ∀ vote ∈ A'.gf_votes s, vote ∉ A.gf_votes s → vote ∈ B.votes)
    (fun s vote hv hn => absurd hv hn)
    (fun A' vote hvB hA' s vote' hv' hn => by
      by_cases hv'' : vote' ∈ A'.gf_votes s
      · exact hA' s vote' hv'' hn
      · rw [on_goldfish_vote_new C P A' t vote s vote' hv' hv'']
        exact hvB)

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- Every answer of the tick of the available chain adds to the pool only a vote it broadcast:
the revocation and the confirmation update keep the pool, and the Goldfish vote duty adds only
the vote it broadcast.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests. -/
theorem ac_on_tick_prov (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBSpec (fun A' l => ∀ s : Slot, ∀ vote ∈ A'.gf_votes s, vote ∉ A.gf_votes s →
        NamedObject.gfVote vote ∈ l)
      (ac_on_tick C P A Φ t v b b') := by
  simp only [ac_on_tick]
  refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBSpec.bind_liftPost (revoke_locks_keepsVotes P _ Φ t _) (fun A₂ h₂ => ?_)
    refine DREBSpec.bind' (goldfish_vote_prov C P A₂ Φ t v) (fun A₃ l₁ h₁ => ?_)
    have h₃ : ∀ s : Slot, ∀ vote ∈ A₃.gf_votes s, vote ∉ A.gf_votes s →
        NamedObject.gfVote vote ∈ l₁ ++ [] := fun s vote hv hn => by
      rw [List.append_nil]
      exact h₁ s vote hv (by rw [h₂.1]; exact hn)
    refine DREBSpec.ite (fun _ => ?_) (fun _ => DREBSpec.pure h₃)
    exact DREBSpec.bind_liftPost (update_confirmation_keepsVotes C P _ Φ t _)
      (fun A₄ h₄ => DREBSpec.pure (fun s vote hv hn => by
        rw [h₄.1] at hv
        exact h₃ s vote hv hn))
  · refine DREBSpec.ite (fun _ => ?_) (fun _ => DREBSpec.pure (fun s vote hv hn => absurd hv hn))
    exact DREBSpec.bind_liftPost (update_confirmation_keepsVotes C P _ Φ t _)
      (fun A₄ h₄ => DREBSpec.pure (fun s vote hv hn => by
        rw [h₄.1] at hv
        exact absurd hv hn))

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a block adds to the pool only votes of the block's `votes`, each with a slot
at most the slot of the admission time.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `B`: the block. -/
theorem ac_on_block_new_slot (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (B : Block V) :
    ∀ s : Slot, ∀ vote ∈ (ac_on_block C P A t B).gf_votes s, vote ∉ A.gf_votes s →
      vote.slot ≤ C.slot t := by
  simp only [ac_on_block, Id.run]
  exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
    (fun A' => ∀ s : Slot, ∀ vote ∈ A'.gf_votes s, vote ∉ A.gf_votes s → vote.slot ≤ C.slot t)
    (fun s vote hv hn => absurd hv hn)
    (fun A' vote _ hA' s vote' hv' hn => by
      by_cases hv'' : vote' ∈ A'.gf_votes s
      · exact hA' s vote' hv'' hn
      · obtain ⟨rfl, hs⟩ := on_goldfish_vote_new_slot C P A' t vote s vote' hv' hv''
        exact hs)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The source `ac_to_fg` answers is a block of the frame's tree: it is the deepest of the fast
blocks in the viable tree.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `fi`: the answer;
  `source`: its source. -/
theorem ac_to_fg_source_mem {C : Config} {A : ACState V} {Φ : Frame V} {t : Time}
    {fi : FGInput V} {source : Block V}
    -- `ac_to_fg` answers `fi`
    (hfi : ac_to_fg C A Φ t = .ok fi)
    -- `fi`'s source is `source`
    (hs : fi.source = some source) :
    source ∈ Φ.tree := by
  simp only [ac_to_fg] at hfi
  obtain ⟨sv, -, h1⟩ := GoldilocksCorrectness.Proofs.Routines.ok_of_bind_eq_ok hfi
  obtain ⟨hd, -, h2⟩ := GoldilocksCorrectness.Proofs.Routines.ok_of_bind_eq_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  rw [← h2] at hs
  have hmem := deepest?_mem hs
  exact (Finset.mem_filter.mp (Finset.mem_inter.mp hmem).2).1

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the tick of the available chain of `v` at the time `t` sends: at most one object, a
Goldfish vote of `v` for the slot of `t`, and only when `t` is the vote time of that slot,
`C.t_ (C.slot t) + C.Δ`. The revocation and the confirmation update send nothing; the Goldfish
vote duty runs only at the vote time.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests;
- `h`: the root the vote names.

Read aloud: the tick of the available chain sends at most `v`'s Goldfish vote for the slot of `t`,
and only at that slot's vote time. -/
theorem ac_on_tick_sends (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBEmits (fun l => l.length ≤ 1 ∧
        ∀ o ∈ l, (∃ h : BlockId, o = NamedObject.gfVote (GoldfishVote.mk v (C.slot t) h)) ∧
          t = C.t_ (C.slot t) + C.Δ)
      (ac_on_tick C P A Φ t v b b') := by
  simp only [ac_on_tick]
  refine DREBEmits.ite (fun hc => ?_) (fun _ => ?_)
  · have ht : t = C.t_ (C.slot t) + C.Δ := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    refine DREBEmits.bind_nil (DREBEmits.liftM _)
      (fun _ => ?_)
    refine (DREBEmits.bind (L₂ := (· = [])) (goldfish_vote_sends C P _ _ t v)
      (fun _ => ?_)).mono ?_
    · repeat' first
        | exact DREBEmits.pure rfl
        | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
        | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    · rintro _ ⟨l₁, l₂, rfl, ⟨h1, h2⟩, rfl⟩
      rw [List.append_nil]
      exact ⟨h1, fun o ho => ⟨h2 o ho, ht⟩⟩
  · repeat' first
      | exact DREBEmits.pure ⟨Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩
      | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the tick of the available chain of `v` at `t` sends, when `t` is the vote time of its
slot, the vote's wake test `b` passes and `v` is a member of the committee of that slot: a
Goldfish vote of `v` for that slot.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests.

Read aloud: at the vote time, an awake committee member's tick of the available chain sends its
vote. -/
theorem ac_on_tick_emits_vote (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBEmits (fun l => t = C.t_ (C.slot t) + C.Δ → b = true → v ∈ P.committee (C.slot t) →
        ∃ h : BlockId, NamedObject.gfVote (GoldfishVote.mk v (C.slot t) h) ∈ l)
      (ac_on_tick C P A Φ t v b b') := by
  by_cases hc : t = C.t_ (C.slot t) + C.Δ ∧ b = true
  · simp only [ac_on_tick]
    refine DREBEmits.ite (fun _ => ?_) (fun hc' => absurd (by
      rw [Bool.and_eq_true]; exact ⟨decide_eq_true hc.1, hc.2⟩) hc')
    refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    refine (DREBEmits.bind (L₂ := (· = [])) (goldfish_vote_emits_vote C P _ _ t v)
      (fun _ => ?_)).mono ?_
    · repeat' first
        | exact DREBEmits.pure rfl
        | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
        | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    · rintro _ ⟨l₁, l₂, rfl, h1, rfl⟩ _ _ hK
      obtain ⟨h, hh⟩ := h1 hK
      exact ⟨h, by rw [List.append_nil]; exact hh⟩
  · exact (ac_on_tick_sends C P A Φ t v b b').mono (fun _ _ ht hb => absurd ⟨ht, hb⟩ hc)

end

end GoldilocksCorrectness.Proofs.Routines
