module
public import Proofs.Vocabulary.Protocol.Handlers.BlockAdmission
public import Proofs.Vocabulary.Protocol.Handlers.ConfirmationPolicy
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Slot bounds for blocks a named store holds

Along the chain of a held block, slots strictly increase, because the block handler refuses a block
whose parent's slot is not smaller and every store is parent-closed.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace NamedSlotFreshness

open Internal Execution Protocol Proofs.Optimistic
variable {V : Type} [DecidableEq V] [Fintype V]

set_option linter.unusedVariables false in
theorem ancestor_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {t : Time} {X B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v t).T)
    (hXB : Block.Preceq X B) :
    X ∈ (rho.storeBeforeTime S v t).T := by
  have hpc : ParentClosed (rho.storeBeforeTime S v t).core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t v
  exact Proofs.Records.mem_of_preceq
    ((parentClosed_iff (rho.storeBeforeTime S v t).core).mp hpc).2 X B hB hXB

theorem parent_slot_lt_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {t : Time} {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v t).T)
    (hne : B ≠ Block.genesis) :
    B.parent.slot < B.slot := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed t
  have hBn : B ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hB
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hBn
  have hprocessed : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hD
  rcases Protocol.acceptsAt_block_of_processed S rho v n D hprocessed with
      hgenesis | ⟨i, -, t', hacc⟩
  · exact absurd (hDe.symm.trans (by rw [hgenesis]; rfl)) hne
  · simpa only [hDe] using Protocol.parent_slot_lt_of_acceptsAt_block S hacc

/-- Every ancestor of a block a store holds has a slot at most that block's own. -/
theorem preceq_slot_le_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {t : Time} :
    ∀ B : Block V, B ∈ (rho.storeBeforeTime S v t).T →
      ∀ X : Block V, Block.Preceq X B → X.slot ≤ B.slot := by
  intro B
  induction B with
  | genesis =>
      intro _ X hX
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at hX
      exact hX ▸ Nat.le_refl _
  | node p s r gv support ats i ih =>
      intro hB X hX
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hX
      rcases hX with rfl | hXp
      · exact Nat.le_refl _
      · have hpmem : p ∈ (rho.storeBeforeTime S v t).T :=
          ancestor_mem_storeBeforeTime S adm hB
            (Protocol.preceq_of_parent?
              (show (Block.node p s r gv support ats i).parent? = some p from
                rfl))
        have hlt : (Block.node p s r gv support ats i).parent.slot <
            (Block.node p s r gv support ats i : Block V).slot :=
          parent_slot_lt_of_mem_storeBeforeTime S adm hB
            (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
        simp only [Block.parent, Block.slot] at hlt
        exact (ih hpmem X hXp).trans (Nat.le_of_lt hlt)

/-- A strict ancestor of a held block has a strictly smaller slot. -/
theorem slot_lt_of_preceq_ne_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {t : Time} {A B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v t).T)
    (hAB : Block.Preceq A B) (hne : A ≠ B) :
    A.slot < B.slot := by
  cases B with
  | genesis =>
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at hAB
      exact absurd hAB hne
  | node p s r gv support ats i =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact absurd rfl hne
      · have hpmem : p ∈ (rho.storeBeforeTime S v t).T :=
          ancestor_mem_storeBeforeTime S adm hB
            (Protocol.preceq_of_parent?
              (show (Block.node p s r gv support ats i).parent? = some p from
                rfl))
        have hlt : (Block.node p s r gv support ats i).parent.slot <
            (Block.node p s r gv support ats i : Block V).slot :=
          parent_slot_lt_of_mem_storeBeforeTime S adm hB
            (by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
        simp only [Block.parent, Block.slot] at hlt
        exact lt_of_le_of_lt
          (preceq_slot_le_of_mem_storeBeforeTime S adm p hpmem A hAp) hlt

theorem proposal_time_le_of_acceptsAt_block
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
    Protocol.proposal_time S.E B.erase.slot ≤ t := by
  have hacc' := hacc
  obtain ⟨hhandle, hpre, hpost⟩ := hacc
  obtain ⟨hindex, e, he, hnode, htime⟩ := hhandle
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
  rcases hindex with htick | hdeliver
  · obtain ⟨t', htick, hem⟩ := htick
    have hemit : NamedRun.emits S rho v (.block B) t' := ⟨i, htick, hem⟩
    have hshape := Proofs.HealingSurface.emits_block_shape S rho hemit
    have ht' : t' = t := by
      have heq : Event.tick v t' = e := Option.some.inj (htick.symm.trans he)
      simpa [Event.time, NamedEvent.time] using (congrArg Event.time heq).trans htime
    exact (Proofs.NamedWire.erase_slot B) ▸ (hshape.2.1.symm.trans ht').le
  · obtain ⟨t', hdeliver⟩ := hdeliver
    have heq : Event.deliver v (.block B) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have ht' : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have heDeliver : rho.events[i]? = some (Event.deliver v (.block B) t) := by
      simpa [heq] using he
    have hfuture := (delivery_guards_of_acceptsAt_block S hacc' heDeliver).1
    have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i v
    unfold Proofs.Optimistic.SlotOfClock at hslot
    have hmono : Protocol.proposal_time S.E B.erase.slot ≤
        Protocol.proposal_time S.E (S.E.slotOf (rho.stateBefore S i v).st.core.t) :=
      proposal_time_mono S.E (by
        rw [← hslot]
        exact Nat.le_of_not_gt hfuture)
    exact le_trans hmono (le_trans
      (proposal_time_slotOf_le S.E
        (stateBefore_store_time_nonneg S adm.toNamedScheduleWellFormed v i))
      (by simpa [Event.time, NamedEvent.time] using
        store_time_le_event_time S adm.toNamedScheduleWellFormed heDeliver v))

/-- A block held at a time at most the proposal time of slot `s`, with `0 < s`, has a slot less than
    `s`. -/
theorem block_slot_lt_of_mem_beforeTime_of_le_proposal
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {s : Slot} {t : Time} (hs : 0 < s)
    (ht : t ≤ Protocol.proposal_time S.E s) {C : Block V}
    (hC : C ∈ (rho.storeBeforeTime S v t).T) : C.slot < s := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed t
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hC
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hCn
  have hprocessed : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hD
  rcases acceptsAt_block_of_processed S rho v n D hprocessed with hgen | hacc
  · subst D
    simp only [NamedBlock.erase] at hDe
    subst C
    simpa [Block.slot] using hs
  · obtain ⟨i, hin, time, hacc⟩ := hacc
    obtain ⟨_, e, he, _, het⟩ := hacc.1
    have htime : time < Protocol.proposal_time S.E s := by
      rw [← het]
      exact (hbefore i e hin he).trans_le ht
    by_contra hnot
    have hslot : s ≤ D.erase.slot := by rw [hDe]; exact Nat.le_of_not_gt hnot
    exact (not_lt_of_ge ((proposal_time_mono S.E hslot).trans
      (proposal_time_le_of_acceptsAt_block S adm hacc))) htime

/-- When a held block's slot is at most the candidate's slot, `advance_confirmed` returns the
    candidate. -/
theorem advance_eq_candidate_of_held_slot
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {t : Time} {old candidate : Block V}
    (hold : old ∈ (rho.storeBeforeTime S v t).T)
    (hslot : old.slot ≤ candidate.slot) :
    Protocol.advance_confirmed old candidate = candidate := by
  apply Proofs.ConfirmationPolicy.advance_eq_candidate_of_slot old candidate hslot
  intro hpre hne
  exact slot_lt_of_preceq_ne_of_mem_storeBeforeTime S adm hold hpre hne

end NamedSlotFreshness
end Proofs
end DecoupledConsensusModel

end
