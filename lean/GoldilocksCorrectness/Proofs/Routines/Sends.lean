module
public import Goldilocks.Config

@[expose] public section

/-!
# The Goldfish votes among the objects a duty sends

`isGfVote o`: the object `o` is a Goldfish vote; `NoVote l`: no object of the list `l` is a
Goldfish vote; `TickVotes C v t l`: `l` holds at most one Goldfish vote, `v`'s for the slot of
`t`, sent at that slot's vote time; `Carried o vote`: the object `o` is the Goldfish vote `vote`,
or a block whose `votes` holds `vote`. The lemmas `noVote_…` and `tickVotes_of_append` compose
them over appended lists.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `Carried o vote`: the object `o` is the Goldfish vote `vote`, or a block whose `votes` holds
`vote`.

Read aloud: `o` carries `vote`, as itself or inside a block. -/
def Carried (o : NamedObject V) (vote : GoldfishVote V) : Prop :=
  o = NamedObject.gfVote vote ∨ ∃ B : Block V, o = NamedObject.block B ∧ vote ∈ B.votes

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `isGfVote o`: the object `o` is a Goldfish vote.

Read aloud: `o` is a Goldfish vote. -/
def isGfVote : NamedObject V → Bool
  | .gfVote _ => true
  | _ => false

/-- `NoVote l`: no object of the list `l` is a Goldfish vote.

Read aloud: `l` holds no Goldfish vote. -/
def NoVote (l : List (NamedObject V)) : Prop :=
  ∀ o ∈ l, isGfVote o = false

/-- `TickVotes C v t l`: every Goldfish vote of the list `l` is of the validator `v`, for the slot
of `t`, and `t` is that slot's vote time; and `l` holds at most one Goldfish vote.

Read aloud: `l` holds at most one Goldfish vote, `v`'s for the slot of `t`, sent at that slot's
vote time. -/
def TickVotes (C : Config) (v : V) (t : Time) (l : List (NamedObject V)) : Prop :=
  (∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
      vote.val_index = v ∧ vote.slot = C.slot t ∧ t = C.t_ (C.slot t) + C.Δ) ∧
    (l.filter isGfVote).length ≤ 1

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The empty list holds no Goldfish vote. -/
theorem noVote_nil : NoVote ([] : List (NamedObject V)) :=
  fun _ h => absurd h List.not_mem_nil

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- Two lists without Goldfish votes append to one. -/
theorem noVote_append {l₁ l₂ : List (NamedObject V)} (h₁ : NoVote l₁) (h₂ : NoVote l₂) :
    NoVote (l₁ ++ l₂) := fun o ho => by
  rcases List.mem_append.mp ho with ho | ho
  · exact h₁ o ho
  · exact h₂ o ho

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A list holding one block, then a list without Goldfish votes, holds no Goldfish vote. -/
theorem noVote_block_append {l : List (NamedObject V)}
    (h : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (∃ B : Block V, l₁ = [NamedObject.block B]) ∧ NoVote l₂) :
    NoVote l := by
  obtain ⟨l₁, l₂, rfl, ⟨B, rfl⟩, h₂⟩ := h
  exact noVote_append (fun o ho => by rw [List.mem_singleton.mp ho]; rfl) h₂

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- At most one attestation, then a list without Goldfish votes, holds no Goldfish vote. -/
theorem noVote_attest_append {l : List (NamedObject V)}
    (h : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (l₁ = [] ∨ ∃ a : Attestation V, l₁ = [NamedObject.attest a]) ∧
      NoVote l₂) : NoVote l := by
  obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := h
  refine noVote_append ?_ h₂
  rcases h₁ with rfl | ⟨a, rfl⟩
  · exact noVote_nil
  · exact fun o ho => by rw [List.mem_singleton.mp ho]; rfl

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- What the tick of the available chain sends, then a list without Goldfish votes, satisfies
`TickVotes`. -/
theorem tickVotes_of_append {C : Config} {v : V} {t : Time} {l : List (NamedObject V)}
    (h : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (l₁.length ≤ 1 ∧
        ∀ o ∈ l₁, (∃ h : BlockId, o = NamedObject.gfVote (GoldfishVote.mk v (C.slot t) h)) ∧
          t = C.t_ (C.slot t) + C.Δ) ∧ NoVote l₂) :
    TickVotes C v t l := by
  obtain ⟨l₁, l₂, rfl, ⟨hlen, h₁⟩, h₂⟩ := h
  refine ⟨fun vote hv => ?_, ?_⟩
  · rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨⟨h', he⟩, ht⟩ := h₁ _ hv
      cases he
      exact ⟨rfl, rfl, ht⟩
    · exact absurd (h₂ _ hv) (by simp [isGfVote])
  · have hnil : l₂.filter isGfVote = [] :=
      List.filter_eq_nil_iff.mpr (fun o ho => by rw [h₂ o ho]; exact Bool.false_ne_true)
    rw [List.filter_append, hnil, List.append_nil]
    exact le_trans (List.length_filter_le _ _) hlen

end

end

end GoldilocksCorrectness.Proofs.Routines
