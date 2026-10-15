module
public import Proofs.Vocabulary.Protocol.Handlers.Blocks
public import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
public import Proofs.Vocabulary.Objects.AdmissibleCore
public import Proofs.Vocabulary.ModelProperties.NamedNode_tick
public import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Execution.ReceiptCallsBase
import Proofs.Vocabulary.Execution.Wire
import Proofs.Vocabulary.Generic.Sync
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Proofs.Vocabulary.Protocol.Handlers.Pool
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Vocabulary.ModelProperties.NamedReceipt_processed

@[expose] public section

/-!
# Block admission at the receiver

The local step from a delivered block to its membership in the receiver's tree, and the checks every
accepted block passed.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Behaviour of the checked handler -/

omit [Fintype V] in
private theorem commitBlock_self_bodies (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.commitBlock st st.core B).bodies = st.bodies := by
  unfold Protocol.NamedStore.commitBlock
  split
  · rename_i h
    exact False.elim (h.1 h.2)
  · rfl

/-- The bodies after `on_block_with` are the bodies after `process_block_core`. -/
private theorem on_block_with_bodies
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).bodies =
      (Protocol.NamedStore.process_block_core E hc cfg st B).bodies := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact (admit_rows_bodies_and_core_T hc B.attestations _).1
  · rfl

/-- A fresh named body admitted by `on_block_with` has a slot at most the store's slot, the proposer
    of its slot, a parent of earlier slot, and admissible carried attestations. -/
private theorem new_body_guards
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg st B).bodies) :
    B.erase.slot ≤ st.core.s ∧
      B.erase.proposer? = some (E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot ∧
      Protocol.carried_attestations_admissible hc B.erase = true := by
  rw [on_block_with_bodies] at hpost
  unfold Protocol.NamedStore.process_block_core at hpost
  by_cases hp : B.parent ∈ st.bodies
  · simp only [hp, not_true_eq_false, if_false] at hpost
    by_cases ha : Protocol.carried_attestations_admissible hc B.erase = true
    · simp only [Protocol.on_block_checked_using, ha, if_true] at hpost
      by_cases hfirst : st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
          B.erase.parent ∉ st.core.T
      · simp only [Protocol.on_block_using, hfirst, if_true,
          commitBlock_self_bodies] at hpost
        exact False.elim (hpre hpost)
      · by_cases hfinal : (!Block.preceq st.core.F B.erase) = true
        · simp only [Protocol.on_block_using, hfirst, if_false, hfinal, if_true,
            commitBlock_self_bodies] at hpost
          exact False.elim (hpre hpost)
        · have hfinalFalse : (!Block.preceq st.core.F B.erase) = false :=
            Bool.eq_false_of_not_eq_true hfinal
          by_cases hproposer :
            B.erase.proposer? ≠ some (E.proposer B.erase.slot)
          · simp [Protocol.on_block_using, hfirst, hfinalFalse,
              hproposer, commitBlock_self_bodies] at hpost
            exact False.elim (hpre hpost)
          · by_cases hparent : ¬ B.erase.parent.slot < B.erase.slot
            · simp [Protocol.on_block_using, hfirst, hfinalFalse,
                hproposer, hparent, commitBlock_self_bodies] at hpost
              exact False.elim (hpre hpost)
            · exact ⟨Nat.le_of_not_gt (fun h => hfirst (Or.inl h)),
                not_not.mp hproposer, not_not.mp hparent, ha⟩
    · have haf : Protocol.carried_attestations_admissible hc B.erase = false :=
        Bool.eq_false_of_not_eq_true ha
      simp only [Protocol.on_block_checked_using, haf, Bool.false_eq_true,
        if_false, commitBlock_self_bodies] at hpost
      exact False.elim (hpre hpost)
  · simp only [hp] at hpost
    exact False.elim (hpre hpost)

/-- Given its named parent, freshness, and the handler's checks, `on_block_with` inserts the named
    body `B`. -/
private theorem handler_inserts
    (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hp : B.parent ∈ st.bodies) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s) (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried : Protocol.carried_attestations_admissible S.hc B.erase = true) :
    B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  have hparentTree : B.erase.parent ∈ st.core.T := by
    rw [Proofs.NamedWire.erase_parent, hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hp
  have hfirst : ¬ (st.core.s < B.erase.slot ∨ B.erase ∈ st.core.T ∨
      B.erase.parent ∉ st.core.T) := by
    simp only [not_or]
    exact ⟨Nat.not_lt.mpr hslot, hfresh, not_not.mpr hparentTree⟩
  have hfinal : (!Block.preceq st.core.F B.erase) = false := by rw [hF]; rfl
  have hafter : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase).T := by
    simp [Protocol.on_block_checked_using, hcarried,
      Protocol.on_block_using, hfirst, hfinal, hproposer, hparent,
      Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T S.E]
  rw [on_block_with_bodies]
  unfold Protocol.NamedStore.process_block_core
  rw [if_neg (not_not.mpr hp)]
  unfold Protocol.NamedStore.commitBlock
  rw [if_pos ⟨hfresh, hafter⟩]
  exact Finset.mem_insert_self _ _

omit [Fintype V] in
private theorem named_preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

/-- In a run without root collisions, a named block of the run that an honest `v` does not hold is
    not in `v`'s core tree either. -/
private theorem no_geometry_alias (S : Setup V) (rho : Run V)
    (roots : NamedRootCollisionFree S rho) (i : Nat) (v : V)
    (hv : v ∈ rho.honest) (B : NamedBlock V) (hB : NamedRun.blockInRun S rho B)
    (hnot : B ∉ (NamedRun.stateBefore S rho i v).st.bodies) :
    B.erase ∉ (NamedRun.stateBefore S rho i v).st.core.T := by
  intro hgeom
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
  rw [hcoh.1] at hgeom
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hgeom
  have hCscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hC)
  have hroot : C.root = B.root :=
    (Proofs.NamedWire.erase_root C).symm.trans ((congrArg Block.root he).trans (Proofs.NamedWire.erase_root B))
  have hCB : C = B := roots.root_injective C B hCscope hB C B
    (Or.inl (named_preceq_self C)) (Or.inr (named_preceq_self B)) hroot
  exact hnot (by simpa only [hCB] using hC)

/-- An accepted block has the proposer of its slot, a parent of earlier slot, and admissible carried
    attestations. -/
private theorem guards_of_acceptsAt_block (S : Setup V) {rho : Run V}
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) ta) :
    B.erase.proposer? = some (S.E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot ∧
      Protocol.carried_attestations_admissible S.hc B.erase = true := by
  have hpre : B ∉ (NamedRun.stateBefore S rho i v).st.bodies :=
    (Proofs.ModelProperties.processed_block_eq_false_iff _ B).mp hacc.2.1
  have hpost : B ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies :=
    (Proofs.ModelProperties.processed_block_eq_true_iff _ B).mp hacc.2.2
  rcases hacc.1.1 with ⟨t, htick, hB⟩ | ⟨t, hdeliver⟩
  · have hdue : 0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = v :=
      (Proofs.HealingSurface.block_mem_on_tick_emit S v (NamedRun.stateBefore S rho i v) t hB).1
    set n := NamedRun.stateBefore S rho i v with hn
    set c := DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache with hcdef
    have hstage := tick_bodies_and_coreT_from_proposal
      (DecoupledConsensusModel.Protocol.frameContract c) S (S.node v) n.st n.record t
    rw [Proofs.NamedRuntime.stateBefore_tick S rho htick,
      Proofs.ModelProperties.tick_fst_st_frameContract] at hpost
    change B ∈ (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract c)
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.bodies at hpost
    rw [hstage.1] at hpost
    have hdue' : 0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node v).val_index := by
      refine ⟨hdue.1, hdue.2.1, ?_⟩
      rw [hdue.2.2, S.node_val_index]
    simp only [if_pos hdue'] at hpost
    have heq := Proofs.NamedReceiptCallsBase.self_proposal_call S rho htick hB
    have heqStore := congrArg Prod.fst heq
    rw [heqStore] at hpost
    have hpre' : B ∉ (Protocol.NamedStore.setClock S.E n.st t).bodies := by
      rw [Proofs.ModelProperties.setClock_bodies]
      exact hpre
    exact (new_body_guards S.E S.hc S.cfg _ B hpre' hpost).2
  · rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hdeliver] at hpost
    rw [Proofs.ModelProperties.process_block] at hpost
    exact (new_body_guards S.E S.hc S.cfg _ B hpre hpost).2

/-- An accepted block has the proposer of its slot. -/
theorem proposer_eq_of_acceptsAt_block
    (S : Setup V) {rho : Run V} {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
    B.erase.proposer? = some (S.E.proposer B.erase.slot) :=
  (guards_of_acceptsAt_block S hacc).1

/-- An accepted block's parent has an earlier slot. -/
theorem parent_slot_lt_of_acceptsAt_block
    (S : Setup V) {rho : Run V} {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
    B.erase.parent.slot < B.erase.slot :=
  (guards_of_acceptsAt_block S hacc).2.1

/-- An accepted block's carried attestations are admissible. -/
theorem carried_attestations_admissible_of_acceptsAt_block
    (S : Setup V) {rho : Run V} {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
    Protocol.carried_attestations_admissible S.hc B.erase = true :=
  (guards_of_acceptsAt_block S hacc).2.2

/-- A block accepted by a delivery has a slot not later than the receiver's, admissible carried
    attestations, the proposer of its slot, and a parent of earlier slot. -/
theorem delivery_guards_of_acceptsAt_block
    (S : Setup V) {rho : Run V} {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t)
    (hi : rho.events[i]? = some (Event.deliver v (.block B) t)) :
    ¬ (NamedRun.stateBefore S rho i v).st.core.s < B.erase.slot ∧
      Protocol.carried_attestations_admissible S.hc B.erase = true ∧
      B.erase.proposer? = some (S.E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot := by
  have hpre : B ∉ (NamedRun.stateBefore S rho i v).st.bodies :=
    (Proofs.ModelProperties.processed_block_eq_false_iff _ _).mp hacc.2.1
  have hpost : B ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies :=
    (Proofs.ModelProperties.processed_block_eq_true_iff _ _).mp hacc.2.2
  rw [Proofs.NamedReceiptCallsBase.delivery_result S rho hi, Proofs.ModelProperties.process_block] at hpost
  obtain ⟨hslot, hproposer, hparent, hvalid⟩ := new_body_guards S.E S.hc S.cfg _ B hpre hpost
  exact ⟨Nat.not_lt.mpr hslot, hvalid, hproposer, hparent⟩

/-- The clock of every run-prefix store is nonnegative. -/
theorem stateBefore_store_time_nonneg (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) (i : Nat) :
    0 ≤ (NamedRun.stateBefore S rho i v).st.core.t := by
  rw [store_time_eq_lastTick S rho v i]
  cases hl : Run.lastTickIn v (rho.events.take i) with
  | none => simp
  | some p =>
      simp only [Option.getD]
      have hp : Event.tick v p ∈ rho.events :=
        (List.take_sublist i rho.events).mem (tick_mem_of_lastTickIn v _ hl)
      exact (sch.in_horizon _ hp).1

/-- At every state of a run, the store's slot is the slot of its clock. -/
private theorem stateBefore_slot_clock (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    (NamedRun.stateBefore S rho i v).st.core.s =
      S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t := by
  induction i with
  | zero =>
      simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
        Protocol.NamedStore.initial, Protocol.Store.init, Env.slotOf, slotOfTime]
  | succ i ih =>
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases he : rho.events[i]? with
      | none => simpa only [Option.toList_none, List.foldl_nil] using ih
      | some e =>
          change (NamedWorld.step S (NamedRun.stateBefore S rho i) e v).st.core.s =
            S.E.slotOf (NamedWorld.step S (NamedRun.stateBefore S rho i) e v).st.core.t
          by_cases hv : e.node = v
          · cases e with
            | tick u t =>
                change u = v at hv
                subst u
                rw [Proofs.NamedRuntime.step_tick]
                rw [(Proofs.NamedNode.tick_clock S v _ t).1, (Proofs.NamedNode.tick_clock S v _ t).2]
            | deliver u o t =>
                change u = v at hv
                subst u
                rw [Proofs.NamedRuntime.step_deliver]
                rw [(Proofs.NamedNode.process_clock S _ o).1, (Proofs.NamedNode.process_clock S _ o).2]
                exact ih
          · rw [Proofs.NamedRuntime.step_other S _ e v (Ne.symm hv)]
            exact ih

/-- At an honest receiver, a delivery of `B` at or after the proposal time of `B`'s slot does not
    find `B`'s slot later than the store's slot. -/
theorem not_future_of_delivery_after_proposal_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (.block B) t))
    (hlo : Protocol.proposal_time S.E B.erase.slot ≤ t) :
    ¬ (NamedRun.stateBefore S rho i v).st.core.s < B.erase.slot := by
  have htick : Event.tick v (Protocol.proposal_time S.E B.erase.slot) ∈ rho.events :=
    adm.tick_total v hv _ (Proofs.Optimistic.publicTime_proposal_time S B.erase.slot)
      (Proofs.Optimistic.proposal_time_nonneg S.E B.erase.slot)
      (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : Protocol.proposal_time S.E B.erase.slot ≤
      (NamedRun.stateBefore S rho i v).st.core.t :=
    tick_le_store_time S adm.toNamedScheduleWellFormed hi htick hlo
  rw [stateBefore_slot_clock S rho i v]
  exact Nat.not_lt.mpr (slot_le_slotOf_of_proposal_time_le S.E hclock)

/-- A block is accepted at or after the proposal time of its slot. -/
theorem proposal_time_le_of_acceptsAt_block
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
    Protocol.proposal_time S.E B.erase.slot ≤ t := by
  obtain ⟨e, he, -, ht⟩ := hacc.1.2
  rcases hacc.1.1 with ⟨t', htick, hB⟩ | ⟨t', hdeliver⟩
  · have heq : e = Event.tick v t' := Option.some.inj (he.symm.trans htick)
    have ht' : t' = t := by
      rw [heq] at ht; exact ht
    have hemit : Run.emits S rho v (.block B) t' := ⟨i, htick, hB⟩
    have hshape := Proofs.HealingSurface.emits_block_shape S rho hemit
    rw [Proofs.NamedWire.erase_slot]
    exact (hshape.2.1.symm.trans ht').le
  · have heq : e = Event.deliver v (.block B) t' := Option.some.inj (he.symm.trans hdeliver)
    have ht' : t' = t := by
      rw [heq] at ht; exact ht
    have heDeliver : rho.events[i]? = some (Event.deliver v (.block B) t) := ht' ▸ hdeliver
    have hfuture := (delivery_guards_of_acceptsAt_block S hacc heDeliver).1
    rw [stateBefore_slot_clock S rho i v] at hfuture
    have hmono : Protocol.proposal_time S.E B.erase.slot ≤
        Protocol.proposal_time S.E
          (S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t) :=
      proposal_time_mono S.E (Nat.not_lt.mp hfuture)
    refine le_trans hmono (le_trans
      (proposal_time_slotOf_le S.E
        (stateBefore_store_time_nonneg S adm.toNamedScheduleWellFormed v i)) ?_)
    exact store_time_le_event_time S adm.toNamedScheduleWellFormed heDeliver v

/-- A delivery of `B` is an accepting event of `B` when, in the receiver's store before the event,
    `B`'s slot is not later than the store's slot, the finalized block precedes `B`, and `B` has the
    proposer of its slot, a parent of earlier slot, and admissible carried attestations. -/
theorem acceptsAt_block_of_delivery_guards_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block B) t))
    (hslot : ¬ (NamedRun.stateBefore S rho i v).st.core.s < B.erase.slot)
    (hF : Block.Preceq (NamedRun.stateBefore S rho i v).st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparentSlot : B.erase.parent.slot < B.erase.slot)
    (hattestations : Protocol.carried_attestations_admissible S.hc B.erase = true) :
    NamedRun.acceptsAt S rho i v (Object.block B) t := by
  have hparent : B.parent ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
    have hdeps := adm.deps i v (Object.block B) t hi
    simpa only [NamedReceipt.depsPresent, decide_eq_true_eq] using hdeps
  have hfresh : B ∉ (NamedRun.stateBefore S rho i v).st.bodies := by
    have hf := adm.fresh i v (Object.block B) t hi
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hf
  have hv : v ∈ rho.honest := by
    have h := adm.honest_only _ (List.mem_of_getElem? hi)
    simpa only [NamedEvent.node] using h
  have hscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_delivery S rho hi)
  have hlegacyFresh : B.erase ∉ (NamedRun.stateBefore S rho i v).st.core.T :=
    no_geometry_alias S rho adm.toNamedRootCollisionFree i v hv B hscope hfresh
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
  have hnew := handler_inserts S (NamedRun.stateBefore S rho i v).st B hcoh hparent hlegacyFresh
    (Nat.not_lt.mp hslot) hF hproposer hparentSlot hattestations
  refine ⟨⟨Or.inr ⟨t, hi⟩, Event.deliver v (Object.block B) t, hi, rfl, rfl⟩, ?_, ?_⟩
  · simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hfresh
  · have hstate : (NamedRun.stateBefore S rho (i + 1) v).st =
        NamedReceipt.process S (NamedRun.stateBefore S rho i v).st (Object.block B) :=
      Proofs.NamedReceiptCallsBase.delivery_result S rho hi
    rw [hstate]
    simpa only [NamedReceipt.process, NamedReceipt.processed, decide_eq_true_eq] using hnew


end Protocol
end DecoupledConsensusModel

end
