import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Record.Wiring

/-!
# Goldfish votes and support cutoffs

`ConeSupport` from the votes of an honest committee majority, support cutoffs increasing with the
slot, and the slot of the vote-duty store, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- If the honest members of slot `s`'s committee are a strict majority of it,
    `support ⊆ votes ⊆ late`, no honest member equivocates in `votes`, and every honest member cast
    a vote in `support` for a block of `T` satisfying `tgt` with slot at most `s`, then
    `ConeSupport` holds. -/
theorem Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes (facts : Record.Facts M) {E : Env V} {T : Finset (Block V)}
    {votes support late : Finset (GoldfishVote V)} {s : Slot} {Hon : Finset V}
    {tgt : Block V → Prop}
    (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card)
    (hsub : votes ⊆ late) (hss : support ⊆ votes)
    (hne : ∀ x ∈ E.committee s, x ∈ Hon → M.equivocates votes x = false)
    (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ X : Block V, tgt X ∧
      X.slot ≤ s ∧ (⟨x, s, X.root⟩ : GoldfishVote V) ∈ support ∧
      Block.find? T X.root = some X) :
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M E T votes support late s Hon tgt where
  majority := hmaj
  counted := hsub
  sub := hss
  no_equiv := hne
  vote := by
    intro x hx hxH
    obtain ⟨X, htgt, hXslot, hmem, hfind⟩ := hvote x hx hxH
    exact ⟨⟨x, s, X.root⟩, hmem, rfl, rfl, X, hfind, hXslot, htgt⟩

/-- If the voters of `late` at slot `s` are fewer than twice the honest members of slot `s`'s
    committee, `support ⊆ votes ⊆ late`, no honest member equivocates in `votes`, and every honest
    member cast a vote in `support` for a block of `T` satisfying `tgt` with slot at most `s`, then
    `ConeSupportCount` holds. -/
theorem Vocabulary.Proofs.Optimistic.coneSupportCount_of_named_votes (facts : Record.Facts M)
    {E : Env V} {T : Finset (Block V)}
    {votes support late : Finset (GoldfishVote V)} {s : Slot} {Hon : Finset V}
    {tgt : Block V → Prop}
    (hcount : M.voters_count E late s < 2 * ((E.committee s) ∩ Hon).card)
    (hsub : votes ⊆ late) (hss : support ⊆ votes)
    (hne : ∀ x ∈ E.committee s, x ∈ Hon → M.equivocates votes x = false)
    (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ X : Block V, tgt X ∧
      X.slot ≤ s ∧ (⟨x, s, X.root⟩ : GoldfishVote V) ∈ support ∧
      Block.find? T X.root = some X) :
    Restated.Vocabulary.Proofs.Optimistic.ConeSupportCount M E T votes support late s Hon tgt where
  count := hcount
  counted := hsub
  sub := hss
  no_equiv := hne
  vote := by
    intro x hx hxH
    obtain ⟨X, htgt, hXslot, hmem, hfind⟩ := hvote x hx hxH
    exact ⟨⟨x, s, X.root⟩, hmem, rfl, rfl, X, hfind, hXslot, htgt⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- If `a ≤ b`, the support cutoff of slot `a` is at most that of slot `b`. -/
theorem Vocabulary.Proofs.Optimistic.support_cutoff_mono (facts : Record.Facts M) (E : Env V) {a b : Slot} (h : a ≤ b) :
    M.support_cutoff E a ≤ M.support_cutoff E b :=
  facts.sch.support_cutoff_mono E h

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Optimistic
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

/-- Every store of validator `w`'s vote duty at slot `s` has slot `s`. -/
theorem Vocabulary.Proofs.Optimistic.voteDutyStore_slot (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) (w : V) (s : Slot) : ∀ w₁ ∈ Restated.Vocabulary.Proofs.Optimistic.voteDutyStore M S ρ w s, 
    w₁.s = s := by
  intro w₁ hw₁
  obtain ⟨ns, -, rfl⟩ := hw₁
  exact Restated.Vocabulary.Proofs.Optimistic.voteStore_slot facts S ns.core s

end

end DecoupledConsensusModel.Sts.Restated
