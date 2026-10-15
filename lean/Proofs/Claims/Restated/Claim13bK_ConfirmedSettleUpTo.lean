import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Record.Wiring

/-!
# Confirmed blocks that settle on honest votes, up to a slot

How `AncestorOfHonestHeadsFromTo`, the condition over the slots from `s` to an upper slot `sEnd`,
passes to ancestors, to later slots and through the routines that update the stable and confirmed
records, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest active committee member of every slot from `s` to `sEnd` votes for a descendant
    of `B`, and `sEnd' ≤ sEnd`, the same holds from `s` to `sEnd'`. -/
theorem AncestorOfHonestHeadsFromTo.mono_end (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {B : Block V} {s sEnd sEnd' : Slot}
    (hle : sEnd' ≤ sEnd) (h : Restated.AncestorOfHonestHeadsFromTo M S Sched x B s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x B s sEnd' :=
  fun s' hs' hs'' => h s' hs' (le_trans hs'' hle)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest active committee member of every slot from `s` to `sEnd` votes for a descendant
    of `B`, and `X` is an ancestor of `B`, the same holds of `X`. -/
theorem ancestorOfHonestHeadsFrom_of_preceq_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {X B : Block V} {s sEnd : Slot}
    (hXB : Block.Preceq X B) (h : Restated.AncestorOfHonestHeadsFromTo M S Sched x B s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x X s sEnd :=
  fun s' hs' hs'' => Restated.headsBelow_mono facts S Sched x hXB (h s' hs' hs'')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest active committee member of every slot from `s` to `sEnd` votes for a descendant
    of `B`, the same holds from any slot `s' ≥ s` to `sEnd`. -/
theorem ancestorOfHonestHeadsFrom_mono_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {B : Block V} {s s' sEnd : Slot} (hss' : s ≤ s')
    (h : Restated.AncestorOfHonestHeadsFromTo M S Sched x B s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x B s' sEnd :=
  fun s'' hs'' hs''' => h s'' (le_trans hss' hs'') hs'''

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `G` has `AncestorOfHonestHeadsFromTo` from `s` to `sEnd`, and `old` has it whenever `G` is an
    ancestor of `old`, then `advance_confirmed old G` has it from `s` to `sEnd`. -/
theorem ancestorOfHonestHeadsFrom_advance_confirmed_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {old G : Block V} {s sEnd : Slot}
    (hG : Restated.AncestorOfHonestHeadsFromTo M S Sched x G s sEnd)
    (hold : Block.Preceq G old → Restated.AncestorOfHonestHeadsFromTo M S Sched x old s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.advance_confirmed old G) s sEnd := by
  rcases facts.hd.advance_confirmed_values old G with ⟨h, he⟩ | he
  · rw [he]; exact hold h
  · rw [he]; exact hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `stable` has `AncestorOfHonestHeadsFromTo` from `s` to `sEnd`, and the candidate and `old`
    each have it whenever they are descendants of `stable`, then the block
    `floor_on_stable stable candidate old` returns has it from `s` to `sEnd`. -/
theorem ancestorOfHonestHeadsFrom_floor_on_stable_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {stable candidate old : Block V}
    {s sEnd : Slot}
    (hst : Restated.AncestorOfHonestHeadsFromTo M S Sched x stable s sEnd)
    (hcand : Block.Preceq stable candidate →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x candidate s sEnd)
    (hold : Block.Preceq stable old → Restated.AncestorOfHonestHeadsFromTo M S Sched x old s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.floor_on_stable stable candidate old)
      s sEnd := by
  rcases facts.hd.floor_on_stable_values stable candidate old with ⟨h1, he⟩ | ⟨h2, he⟩ | he
  · rw [he]; exact hcand h1
  · rw [he]; exact hold h2
  · rw [he]; exact hst

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a store's `latest_stable` and its finalized block `F` both have `AncestorOfHonestHeadsFromTo`
    from `s` to `sEnd`, so does `get_stable` of the store. -/
theorem ancestorOfHonestHeadsFrom_get_stable_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (st : M.S) {s sEnd : Slot}
    (hL : Restated.AncestorOfHonestHeadsFromTo M S Sched x st.latest_stable s sEnd)
    (hF : Restated.AncestorOfHonestHeadsFromTo M S Sched x st.F s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_stable st) s sEnd := by
  rcases facts.hd.get_stable_eq_or st with he | he
  · rw [he]; exact hL
  · rw [he]; exact hF

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If a store's `get_stable` has `AncestorOfHonestHeadsFromTo` from `s` to `sEnd`, and its
    `latest_confirmed` has it whenever it is a descendant of `get_stable`, then `get_confirmed` of
    the store has it from `s` to `sEnd`. -/
theorem ancestorOfHonestHeadsFrom_get_confirmed_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (st : M.S) {s sEnd : Slot}
    (hS : Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_stable st) s sEnd)
    (hC : Block.Preceq (M.get_stable st) st.latest_confirmed →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x st.latest_confirmed s sEnd) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_confirmed st) s sEnd := by
  rcases facts.hd.get_confirmed_values st with ⟨h, he⟩ | he
  · rw [he]; exact hC h
  · rw [he]; exact hS

end

end DecoupledConsensusModel.Sts.Restated
