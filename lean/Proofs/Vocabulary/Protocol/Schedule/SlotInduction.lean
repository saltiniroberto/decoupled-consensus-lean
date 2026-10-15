module
public import Proofs.Vocabulary.Protocol.Schedule.Alignment
public import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (HealConfig)
open Internal
open Execution
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## What the honest votes of a slot say -/


/-- `X` is the head of a slot-`s` Goldfish vote that an honest committee member emitted at the
    slot-`s` vote time, and `X` is the erasure of a block of the run. -/
def HonestHead (S : Setup V) (ρ : Run V) (s : Slot) (X : Block V) : Prop :=
  ∃ x ∈ ρ.honest, x ∈ S.E.committee s ∧
    (∃ C : NamedBlock V, C.erase = X ∧ RunBlock S ρ C) ∧
    ρ.emits S x (Object.gfVote ⟨x, s, X.root⟩) (Protocol.vote_time S.E s)


/-- Every honest head of slot `s` resolves in the tree `T` by its root and is stamped in `tb` before
    the slot-`s` support cutoff. -/
def HeadsResolveIn (S : Setup V) (ρ : Run V) (s : Slot) (T : Finset (Block V))
    (tb : TimestampMap (Block V)) : Prop :=
  ∀ X : Block V, HonestHead S ρ s X →
    Block.find? T X.root = some X ∧
      stampedBefore tb (Protocol.support_cutoff S.E s) X = true

/-- `HeadsResolveIn` transfers along equalities of the tree and of the stamp map. -/
theorem HeadsResolveIn.of_eq {S : Setup V} {ρ : Run V} {s : Slot}
    {T T' : Finset (Block V)} {tb tb' : TimestampMap (Block V)}
    (h : HeadsResolveIn S ρ s T tb) (hT : T' = T) (htb : tb' = tb) :
    HeadsResolveIn S ρ s T' tb' := by
  rw [hT, htb]; exact h

/-! ### Membership and root uniqueness give resolution -/

omit [Fintype V] in
/-- `Block.find?` returns a member of `T` whose root no other member carries. -/
theorem find?_eq_some_of_unique {T : Finset (Block V)} {X : Block V} (hX : X ∈ T)
    (huniq : ∀ Y ∈ T, Y.root = X.root → Y = X) :
    Block.find? T X.root = some X := by
  unfold Block.find?
  refine pickUnique?_eq_some hX (by simp) ?_
  intro a ha hp
  exact huniq a ha (of_decide_eq_true hp)

/-- `HeadsResolveIn` holds when every honest head of slot `s` is in `T` and stamped before the
    slot-`s` support cutoff, and no two members of `T` share a root. -/
theorem headsResolveIn_of (S : Setup V) (ρ : Run V) (s : Slot)
    {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    (hmem : ∀ X : Block V, HonestHead S ρ s X → X ∈ T)
    (hinj : ∀ X Y : Block V, X ∈ T → Y ∈ T → X.root = Y.root → X = Y)
    (harr : ∀ X : Block V, HonestHead S ρ s X →
      stampedBefore tb (Protocol.support_cutoff S.E s) X = true) :
    HeadsResolveIn S ρ s T tb :=
  fun X hX =>
    ⟨find?_eq_some_of_unique (hmem X hX)
      (fun Y hY hroot => hinj Y X hY (hmem X hX) hroot), harr X hX⟩


/-! ## Cone support from named votes -/

/-- `ConeSupport` holds when the honest members are a majority of the slot-`s` committee, none
    equivocates in `votes`, and each has a vote in `support` for a target block of slot at most `s`
    that resolves in `T`. -/
theorem coneSupport_of_named_votes {E : Env V} {T : Finset (Block V)}
    {votes support late : Finset (GoldfishVote V)} {s : Slot} {Hon : Finset V}
    {tgt : Block V → Prop}
    (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card)
    (hsub : votes ⊆ late) (hss : support ⊆ votes)
    (hne : ∀ x ∈ E.committee s, x ∈ Hon → Protocol.equivocates votes x = false)
    (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ X : Block V, tgt X ∧
      X.slot ≤ s ∧ (⟨x, s, X.root⟩ : GoldfishVote V) ∈ support ∧
      Block.find? T X.root = some X) :
    ConeSupport E T votes support late s Hon tgt where
  majority := hmaj
  counted := hsub
  sub := hss
  no_equiv := hne
  vote := by
    intro x hx hxH
    obtain ⟨X, htgt, hXslot, hmem, hfind⟩ := hvote x hx hxH
    exact ⟨⟨x, s, X.root⟩, hmem, rfl, rfl, X, hfind, hXslot, htgt⟩

/-! ## Slot-time facts -/

/-- The slot-`s` support cutoff is at most the slot-`(s + 1)` vote time. -/
theorem support_cutoff_le_vote_time_succ (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.vote_time E (s + 1) := by
  have hstep : E.t (s + 1) = E.t s + 4 * E.Δ := by
    unfold Env.t slotStart
    push_cast
    ring
  have key : ∀ a d : Int, 0 < d → a + 2 * d ≤ a + 4 * d + d := by
    intro a d hd; omega
  rw [Protocol.support_cutoff, Protocol.vote_time, hstep]
  exact key (E.t s) E.Δ E.Δ_pos

/-- The slot-`s` support cutoff is `4Δs + 2Δ`. -/
theorem support_cutoff_expand (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = 4 * E.Δ * (s : Time) + 2 * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

/-- Support cutoffs grow with the slot. -/
theorem support_cutoff_mono (E : Env V) {a b : Slot} (h : a ≤ b) :
    Protocol.support_cutoff E a ≤ Protocol.support_cutoff E b := by
  rw [support_cutoff_expand, support_cutoff_expand]
  have hΔ : (0 : Time) ≤ 4 * E.Δ := by
    have key : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by intro d hd; omega
    exact key E.Δ E.Δ_pos
  have key : ∀ x y d : Int, x ≤ y → x + d ≤ y + d := by intro x y d hxy; omega
  exact key _ _ _ (Int.mul_le_mul_of_nonneg_left (Int.ofNat_le.mpr h) hΔ)

/-! ## Store projections -/


omit [Fintype V] in
theorem toHealing_slot (st : Protocol.Store V) : st.toHealing.s = st.s := rfl

/-! ## Votes in the next slot's support view -/

/-- A vote in the slot-`(s - 1)` pool, stamped by `tau` before the slot-`(s - 1)` view freeze, is in
    the slot-`s` voter support view. -/
theorem mem_voter_support_view_of_pool (E : Env V) (gst : Protocol.GoldfishStore V)
    (s : Slot) {u : GoldfishVote V}
    (h : u ∈ beforeCutoff gst.tau (Protocol.view_freeze E (s - 1))
      (gst.pool (s - 1))) :
    u ∈ Protocol.voter_support_view E gst s := by
  rw [Protocol.voter_support_view]
  exact Finset.mem_union_left _ h


/-! ## The vote store's slot -/

theorem voteDutyStore_slot (S : Setup V) (ρ : Run V) (w : V) (s : Slot) :
    (voteDutyStore S ρ w s).s = s :=
  voteStore_slot S _ s


end Optimistic
end Proofs
end DecoupledConsensusModel

end
