module
public import Proofs.Vocabulary.Protocol.Schedule.CrossView
public import Proofs.Vocabulary.Protocol.Handlers.BlockAdmission
public import Proofs.Vocabulary.Protocol.Handlers.Execution
public import Proofs.Vocabulary.Execution.ReceiptCallsBase
public import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Generic.Sync
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Acceptance times of Goldfish votes

A Goldfish vote newly inserted into a store is stamped with the store's clock and is not from a
future slot. From this, an accepted vote's acceptance event is bounded by its stamp, and an
admissible run supplies the acceptance windows used by confirmation.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Vote insertion -/

/-- A store step that preserves the pool invariant, stamps every newly inserted vote with `c`, and
    inserts no vote of a slot later than `k`. -/
private structure VoteInsertStep (c : Time) (k : Slot)
    (st st' : Protocol.Store V) : Prop where
  poolStep : PoolStep st st'
  new_stamp : ∀ (_hstamps : PoolStamps st) (u : GoldfishVote V),
    u ∉ st.gf_votes u.slot → u ∈ st'.gf_votes u.slot →
      st'.timestamp_vote u = some (c : Stamp)
  not_future : ∀ (_hstamps : PoolStamps st) (u : GoldfishVote V),
    u ∉ st.gf_votes u.slot → u ∈ st'.gf_votes u.slot →
      ¬ k < u.slot

namespace VoteInsertStep

omit [DecidableEq V] [Fintype V] in
private theorem refl' (c : Time) (k : Slot) (st : Protocol.Store V) :
    VoteInsertStep c k st st where
  poolStep := PoolStep.refl' st
  new_stamp := by
    intro _ u hpre hpost
    exact absurd hpost hpre
  not_future := by
    intro _ u hpre hpost
    exact absurd hpost hpre

omit [DecidableEq V] [Fintype V] in
private theorem trans' {c : Time} {k : Slot}
    {st st' st'' : Protocol.Store V}
    (h₁ : VoteInsertStep c k st st') (h₂ : VoteInsertStep c k st' st'') :
    VoteInsertStep c k st st'' where
  poolStep := PoolStep.trans' h₁.poolStep h₂.poolStep
  new_stamp := by
    intro hs u hpre hpost
    have hs' := h₁.poolStep hs
    have hs'' := h₂.poolStep hs'.2
    by_cases hmid : u ∈ st'.gf_votes u.slot
    · exact hs''.1.stamp u (c : Stamp) (h₁.new_stamp hs u hpre hmid)
    · exact h₂.new_stamp hs'.2 u hmid hpost
  not_future := by
    intro hs u hpre hpost
    have hs' := h₁.poolStep hs
    by_cases hmid : u ∈ st'.gf_votes u.slot
    · exact h₁.not_future hs u hpre hmid
    · exact h₂.not_future hs'.2 u hmid hpost

omit [DecidableEq V] [Fintype V] in
private theorem of_eq {c : Time} {k : Slot} {st st' : Protocol.Store V}
    (hg : st'.gf_votes = st.gf_votes)
    (hv : st'.timestamp_vote = st.timestamp_vote) (ht : st'.t = st.t) :
    VoteInsertStep c k st st' where
  poolStep := PoolStep.of_eq hg hv ht
  new_stamp := by
    intro _ u hpre hpost
    rw [hg] at hpost
    exact absurd hpost hpre
  not_future := by
    intro _ u hpre hpost
    rw [hg] at hpost
    exact absurd hpost hpre

omit [DecidableEq V] [Fintype V] in
private theorem tickStore (c : Time) (k : Slot) (st : Protocol.Store V)
    (t : Time) (s : Slot) (hle : st.t ≤ t) :
    VoteInsertStep c k st { st with t := t, s := s } where
  poolStep := poolStep_tickStore st t s hle
  new_stamp := by
    intro _ u hpre hpost
    exact absurd hpost hpre
  not_future := by
    intro _ u hpre hpost
    exact absurd hpost hpre

omit [Fintype V] in
/-- A vote newly present after `on_goldfish_vote` is the incoming vote, and neither rejection
    condition held. -/
private theorem new_of_on_goldfish_vote (st : Protocol.Store V)
    (x u : GoldfishVote V) (hpre : u ∉ st.gf_votes u.slot)
    (hpost : u ∈ (Protocol.on_goldfish_vote st x).gf_votes u.slot) :
    u = x ∧
      ¬ (x.slot < st.s - 1 ∨ st.s < x.slot ∨ x ∈ st.gf_votes x.slot) ∧
      ¬ Protocol.equivocates (st.pool x.slot) x.val_index = true := by
  by_cases h₁ : x.slot < st.s - 1 ∨ st.s < x.slot ∨ x ∈ st.gf_votes x.slot
  · rw [show Protocol.on_goldfish_vote st x = st by
      unfold Protocol.on_goldfish_vote
      rw [if_pos h₁]] at hpost
    exact absurd hpost hpre
  by_cases h₂ : Protocol.equivocates (st.pool x.slot) x.val_index = true
  · rw [show Protocol.on_goldfish_vote st x = st by
      unfold Protocol.on_goldfish_vote
      rw [if_neg h₁, if_pos h₂]] at hpost
    exact absurd hpost hpre
  obtain ⟨hgf, -, -⟩ := on_goldfish_vote_insert st x h₁ h₂
  simp only [hgf] at hpost
  split_ifs at hpost with hk
  · rcases List.mem_append.mp hpost with hold | hnew
    · exact absurd hold hpre
    · exact ⟨List.mem_singleton.mp hnew, h₁, h₂⟩
  · exact absurd hpost hpre

omit [Fintype V] in
private theorem onGoldfishVote (c : Time) (k : Slot)
    (st : Protocol.Store V) (x : GoldfishVote V)
    (ht : st.t = c) (hs : st.s = k) :
    VoteInsertStep c k st (Protocol.on_goldfish_vote st x) where
  poolStep := poolStep_on_goldfish_vote st x
  new_stamp := by
    intro _ u hpre hpost
    obtain ⟨hux, h₁, h₂⟩ := new_of_on_goldfish_vote st x u hpre hpost
    subst u
    obtain ⟨-, hts, -⟩ := on_goldfish_vote_insert st x h₁ h₂
    simp [hts, ht]
  not_future := by
    intro _ u hpre hpost
    obtain ⟨hux, h₁, -⟩ := new_of_on_goldfish_vote st x u hpre hpost
    subst u
    have hnf : ¬ st.s < x.slot := fun h => h₁ (Or.inr (Or.inl h))
    simpa only [hs] using hnf

/-- The checked Goldfish vote handler is a `VoteInsertStep`. -/
private theorem onGoldfishVoteChecked (c : Time) (k : Slot) (E : Env V)
    (st : Protocol.Store V) (x : GoldfishVote V)
    (ht : st.t = c) (hs : st.s = k) :
    VoteInsertStep c k st (Protocol.on_goldfish_vote_checked E st x) := by
  unfold Protocol.on_goldfish_vote_checked
  split
  · exact refl' c k st
  · exact onGoldfishVote c k st x ht hs

/-- A fold of the checked Goldfish vote handler is a `VoteInsertStep`. -/
private theorem foldChecked (c : Time) (k : Slot) (E : Env V)
    (l : List (GoldfishVote V)) :
    ∀ st : Protocol.Store V, st.t = c → st.s = k →
      VoteInsertStep c k st
        (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l with
  | nil =>
      intro st _ _
      exact refl' c k st
  | cons x xs ih =>
      intro st ht hs
      rw [List.foldl_cons]
      apply trans' (onGoldfishVoteChecked c k E st x ht hs)
      apply ih
      · simpa only [on_goldfish_vote_checked_time] using ht
      · simpa only [Proofs.Optimistic.on_goldfish_vote_checked_slot] using hs

/-! ## The block handler -/

private theorem onBlockUsing (c : Time) (k : Slot) (E : Env V) (st : Protocol.Store V)
    (B : Block V) (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (ht : st.t = c) (hs : st.s = k) :
    VoteInsertStep c k st (Protocol.on_block_using E st B buildState) := by
  by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_pos hfirst]]
    exact refl' c k st
  by_cases hadmit : (!Block.preceq st.F B) = true
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_neg hfirst, if_pos hadmit]]
    exact refl' c k st
  by_cases hprop : B.proposer? ≠ some (E.proposer B.slot)
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_neg hfirst, if_neg hadmit, if_pos hprop]]
    exact refl' c k st
  by_cases hslot : ¬ B.parent.slot < B.slot
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_neg hfirst, if_neg hadmit, if_neg hprop,
        if_pos hslot]]
    exact refl' c k st
  let stored : Protocol.Store V :=
    { st with
      σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
      T := insert B st.T
      timestamp_block := fun C =>
        if C = B then some (st.t : Stamp) else st.timestamp_block C }
  let unpacked : Protocol.Store V :=
    B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
  have hout : Protocol.on_block_using E st B buildState =
      Protocol.update_finality unpacked (unpacked.σ B) := by
    unfold Protocol.on_block_using
    rw [if_neg hfirst, if_neg hadmit, if_neg hprop, if_neg hslot]
  have hstored : VoteInsertStep c k st stored :=
    of_eq rfl rfl rfl
  have hfold : VoteInsertStep c k stored unpacked := by
    apply foldChecked c k E B.gf_votes stored
    · simpa only [stored] using ht
    · simpa only [stored] using hs
  have hfinal : VoteInsertStep c k unpacked
      (Protocol.update_finality unpacked (unpacked.σ B)) :=
    of_eq (update_finality_gf_votes _ _)
      (update_finality_timestamp_vote _ _) (update_finality_time _ _)
  rw [hout]
  exact trans' (trans' hstored hfold) hfinal

private theorem onBlockCheckedUsing (c : Time) (k : Slot)
    (handle : Protocol.Store V → Protocol.Store V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V) (hh : VoteInsertStep c k st (handle st)) :
    VoteInsertStep c k st (Protocol.on_block_checked_using handle hc st B) := by
  unfold Protocol.on_block_checked_using
  split_ifs
  · exact hh
  · exact refl' c k st

/-! ## The named block handler -/

private theorem processBlockCore (c : Time) (k : Slot) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (ht : st.core.t = c) (hs : st.core.s = k) :
    VoteInsertStep c k st.core
      (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  simp only [Protocol.NamedStore.process_block_core]
  split
  · exact refl' c k st.core
  · rw [commitBlock_core]
    exact onBlockCheckedUsing c k _ hc st.core B.erase
      (onBlockUsing c k E st.core B.erase _ ht hs)

private theorem admitRowStep (c : Time) (k : Slot) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (row : NamedAttestation V) :
    VoteInsertStep c k st.core (Protocol.NamedAdmission.admit_row hc st row).core := by
  rw [admit_row_core]
  exact of_eq (on_sg_vote_gf_votes hc st.core _) (on_sg_vote_timestamp_vote hc st.core _)
    (on_sg_vote_time hc st.core _)

private theorem admitRowsStep (c : Time) (k : Slot) (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      VoteInsertStep c k st.core (Protocol.NamedAdmission.admit_rows hc st rows).core
  | [], st => refl' c k st.core
  | row :: rows, st =>
      trans' (admitRowStep c k hc st row)
        (admitRowsStep c k hc rows (Protocol.NamedAdmission.admit_row hc st row))

private theorem onBlockWith (adm : Protocol.CarriedAdmission) (c : Time) (k : Slot)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V)
    (ht : st.core.t = c) (hs : st.core.s = k) :
    VoteInsertStep c k st.core
      (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core := by
  have hcore := processBlockCore c k E hc cfg st B ht hs
  cases adm with
  | alsoCarried =>
      show VoteInsertStep c k st.core
        (if B ∉ st.bodies ∧
            B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies then
              Protocol.NamedAdmission.admit_rows hc
                (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations
            else Protocol.NamedStore.process_block_core E hc cfg st B).core
      split_ifs
      · exact trans' hcore
          (admitRowsStep c k hc B.attestations
            (Protocol.NamedStore.process_block_core E hc cfg st B))
      · exact hcore

/-! ## The four named duties -/

private theorem namedProposeStep (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (c : Time) (k : Slot)
    (ht : st.core.t = c) (hs : st.core.s = k) :
    VoteInsertStep c k st.core
      (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact refl' c k st.core
  · exact onBlockWith .alsoCarried c k E hc cfg st _ ht hs

private theorem namedVoteStep (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (c : Time) (k : Slot) (ht : st.core.t = c) (hs : st.core.s = k) :
    VoteInsertStep c k st.core
      (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core := by
  show VoteInsertStep c k st.core (Protocol.goldfish_vote_with contract E hc nd st.core).1
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact onGoldfishVoteChecked c k E st.core _ ht hs
  · exact refl' c k st.core

private theorem namedConfirmationStep (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) (c : Time) (k : Slot) :
    VoteInsertStep c k st.core
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core :=
  of_eq rfl rfl rfl

private theorem namedAttestStep (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (c : Time) (k : Slot) :
    VoteInsertStep c k st.core
      (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core := by
  show VoteInsertStep c k st.core (Protocol.NamedAdmission.admit_row hc st _).core
  exact admitRowStep c k hc st _

/-! ## The named tick -/

private def TickHold (base : Protocol.Store V) (t : Time) (k : Slot)
    (st' : Protocol.NamedStore V) : Prop :=
  VoteInsertStep t k base st'.core ∧ st'.core.t = t ∧ st'.core.s = k

private theorem namedProposeHold (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (base : Protocol.Store V) (t : Time) (k : Slot) :
    ∀ st' : Protocol.NamedStore V, TickHold base t k st' →
      TickHold base t k (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st').1 := by
  intro st' h
  obtain ⟨hv, ht, hs⟩ := h
  exact ⟨trans' hv (namedProposeStep contract E hc cfg nd st' t k ht hs),
    (named_propose_clock contract E hc cfg nd st').1.trans ht,
    (named_propose_clock contract E hc cfg nd st').2.trans hs⟩

private theorem namedVoteHold (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (base : Protocol.Store V) (t : Time) (k : Slot) :
    ∀ st' : Protocol.NamedStore V, TickHold base t k st' →
      TickHold base t k (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st').1 := by
  intro st' h
  obtain ⟨hv, ht, hs⟩ := h
  exact ⟨trans' hv (namedVoteStep contract E hc nd st' t k ht hs),
    (named_vote_clock contract E hc nd st').1.trans ht,
    (named_vote_clock contract E hc nd st').2.trans hs⟩

private theorem namedConfirmationHold (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (base : Protocol.Store V) (t : Time) (k : Slot) :
    ∀ (st' : Protocol.NamedStore V) (s : Slot), TickHold base t k st' →
      TickHold base t k (Protocol.NamedDuties.update_confirmation_with contract E hc st' s) := by
  intro st' s h
  obtain ⟨hv, ht, hs⟩ := h
  exact ⟨trans' hv (namedConfirmationStep contract E hc st' s t k),
    (named_confirmation_clock contract E hc st' s).1.trans ht,
    (named_confirmation_clock contract E hc st' s).2.trans hs⟩

private theorem namedAttestHold (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (base : Protocol.Store V) (t : Time) (k : Slot) :
    ∀ (st' : Protocol.NamedStore V) (record : Protocol.NamedRecord),
      TickHold base t k st' →
      TickHold base t k (Protocol.NamedDuties.attest_with contract E hc nd st' record).1 := by
  intro st' record h
  obtain ⟨hv, ht, hs⟩ := h
  exact ⟨trans' hv (namedAttestStep contract E hc nd st' record t k),
    (named_attest_clock contract E hc nd st' record).1.trans ht,
    (named_attest_clock contract E hc nd st' record).2.trans hs⟩

private theorem namedTickHold (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hle : st.core.t ≤ t) :
    TickHold st.core t (E.slotOf t)
      (Protocol.NamedTick.tick contract E hc cfg nd st record t).1 := by
  apply named_tick_preserves (TickHold st.core t (E.slotOf t)) contract E hc cfg nd
    (namedProposeHold contract E hc cfg nd st.core t (E.slotOf t))
    (namedVoteHold contract E hc nd st.core t (E.slotOf t))
    (namedConfirmationHold contract E hc st.core t (E.slotOf t))
    (namedAttestHold contract E hc nd st.core t (E.slotOf t))
    st record t
  exact ⟨tickStore t (E.slotOf t) st.core t (E.slotOf t) hle, rfl, rfl⟩

/-- A tick inserts votes only with the tick's time and slot, including the votes carried by its
    proposed block. -/
private theorem onTickEmit (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (hle : n.st.core.t ≤ t) :
    VoteInsertStep t (S.E.slotOf t) n.st.core (NamedNode.tick S v n t).1.st.core := by
  obtain ⟨gc, hgc⟩ : ∃ gc : Protocol.GradeContract V,
      (NamedNode.tick S v n t).1.st =
        (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) n.st n.record t).1 :=
    ⟨_, rfl⟩
  rw [hgc]
  exact (namedTickHold gc S.E S.hc S.cfg (S.node v) n.st n.record t hle).1

private theorem process (S : Setup V) (n : NamedNodeState V) (o : NamedObject V) :
    VoteInsertStep n.st.core.t n.st.core.s n.st.core
      (NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact onBlockWith .alsoCarried n.st.core.t n.st.core.s S.E S.hc S.cfg n.st B rfl rfl
  | gfVote u => exact onGoldfishVoteChecked n.st.core.t n.st.core.s S.E n.st.core u rfl rfl
  | attest a => exact admitRowStep n.st.core.t n.st.core.s S.hc n.st a

end VoteInsertStep

/-! ## One accepting event -/

/-- A Goldfish acceptance is a delivery stamped with the store's clock before the delivery, or a
    tick stamped with the event time; in both cases the vote is not from a future slot. -/
theorem acceptsAt_gfVote_time_shape
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (hacc : Run.acceptsAt S rho i v (Object.gfVote u) t) :
    (∃ o : Object V,
        rho.events[i]? = some (Event.deliver v o t) ∧
        (rho.stateBefore S (i + 1) v).st.core.timestamp_vote u =
          some ((rho.stateBefore S i v).st.core.t : Stamp) ∧
        ¬ (rho.stateBefore S i v).st.core.s < u.slot) ∨
      (rho.events[i]? = some (Event.tick v t) ∧
        (rho.stateBefore S (i + 1) v).st.core.timestamp_vote u = some (t : Stamp) ∧
        ¬ S.E.slotOf t < u.slot) := by
  have hpre : u ∉ (rho.stateBefore S i v).st.core.gf_votes u.slot := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_false_iff_not,
      Protocol.Store.pool, List.mem_toFinset] using hacc.2.1
  have hpost : u ∈ (rho.stateBefore S (i + 1) v).st.core.gf_votes u.slot := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq,
      Protocol.Store.pool, List.mem_toFinset] using hacc.2.2
  obtain ⟨e, he, hnode, htime⟩ := hacc.1.2
  cases e with
  | deliver w o p =>
      simp only [NamedEvent.node, NamedEvent.time] at hnode htime
      subst w
      subst p
      have hstate : (rho.stateBefore S (i + 1) v).st =
          NamedReceipt.process S (rho.stateBefore S i v).st o :=
        Proofs.NamedReceiptCallsBase.delivery_result S rho he
      have hpost' : u ∈ (NamedReceipt.process S (rho.stateBefore S i v).st o).core.gf_votes
          u.slot := by
        rw [← hstate]; exact hpost
      have hs := poolStamps_stateBefore S adm.toNamedScheduleWellFormed v i
      have hstep := VoteInsertStep.process S (rho.stateBefore S i v) o
      apply Or.inl
      refine ⟨o, he, ?_, hstep.not_future hs u hpre hpost'⟩
      rw [hstate]
      exact hstep.new_stamp hs u hpre hpost'
  | tick w p =>
      simp only [NamedEvent.node, NamedEvent.time] at hnode htime
      subst w
      subst p
      have hstate : rho.stateBefore S (i + 1) v =
          (NamedNode.tick S v (rho.stateBefore S i v) t).1 :=
        Proofs.NamedRuntime.stateBefore_tick S rho he
      have hpost' : u ∈ (NamedNode.tick S v (rho.stateBefore S i v) t).1.st.core.gf_votes
          u.slot := by
        rw [← hstate]; exact hpost
      have hle : (rho.stateBefore S i v).st.core.t ≤ t := by
        simpa [Event.time, NamedEvent.time] using
          store_time_le_event_time S adm.toNamedScheduleWellFormed he v
      have hs := poolStamps_stateBefore S adm.toNamedScheduleWellFormed v i
      have hstep := VoteInsertStep.onTickEmit S v (rho.stateBefore S i v) t hle
      apply Or.inr
      refine ⟨he, ?_, hstep.not_future hs u hpre hpost'⟩
      rw [hstate]
      exact hstep.new_stamp hs u hpre hpost'

/-- Every accepted Goldfish vote is accepted at or after its slot's proposal time. -/
theorem proposal_time_le_of_acceptsAt_gfVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (hacc : Run.acceptsAt S rho i v (Object.gfVote u) t) :
    Protocol.proposal_time S.E u.slot ≤ t := by
  rcases acceptsAt_gfVote_time_shape S adm hacc with
    ⟨o, he, -, hfuture⟩ | ⟨he, -, hfuture⟩
  · have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i v
    unfold Proofs.Optimistic.SlotOfClock at hslot
    have hmono : Protocol.proposal_time S.E u.slot ≤
        Protocol.proposal_time S.E (S.E.slotOf (rho.stateBefore S i v).st.core.t) :=
      proposal_time_mono S.E (by rw [← hslot]; exact Nat.le_of_not_gt hfuture)
    exact le_trans hmono (le_trans
      (proposal_time_slotOf_le S.E
        (stateBefore_store_time_nonneg S adm.toNamedScheduleWellFormed v i))
      (by simpa [Event.time, NamedEvent.time] using
        store_time_le_event_time S adm.toNamedScheduleWellFormed he v))
  · have hmono : Protocol.proposal_time S.E u.slot ≤
        Protocol.proposal_time S.E (S.E.slotOf t) :=
      proposal_time_mono S.E (Nat.le_of_not_gt hfuture)
    exact le_trans hmono (proposal_time_slotOf_le S.E
      (adm.toNamedScheduleWellFormed.in_horizon _ (List.mem_of_getElem? he)).1)

/-- For an honest `v`, a vote whose stamp at a later state is before a public time `Gamma` was
    accepted before `Gamma`. -/
theorem acceptsAt_gfVote_lt_of_stamp_before
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {i n : Nat}
    {u : GoldfishVote V} {t Gamma : Time}
    (hacc : Run.acceptsAt S rho i v (Object.gfVote u) t)
    (hin : i + 1 ≤ n) (hpub : PublicTime S Gamma)
    (hstamp : stampedBefore (rho.stateBefore S n v).st.core.timestamp_vote Gamma u = true) :
    t < Gamma := by
  have hcarry : PoolCarry (rho.stateBefore S (i + 1) v).st.core
      (rho.stateBefore S n v).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed v n hin
  rcases acceptsAt_gfVote_time_shape S adm hacc with
    ⟨o, he, hpostStamp, -⟩ | ⟨he, hpostStamp, -⟩
  · have hlater : (rho.stateBefore S n v).st.core.timestamp_vote u =
        some ((rho.stateBefore S i v).st.core.t : Stamp) :=
      hcarry.stamp u _ hpostStamp
    simp only [stampedBefore, hlater, decide_eq_true_eq] at hstamp
    apply processed_lt_of_store_time_lt S adm.toNamedScheduleWellFormed hv he hpub
    exact WithBot.coe_lt_coe.mp hstamp
  · have hlater : (rho.stateBefore S n v).st.core.timestamp_vote u = some (t : Stamp) :=
      hcarry.stamp u _ hpostStamp
    simp only [stampedBefore, hlater, decide_eq_true_eq] at hstamp
    exact WithBot.coe_lt_coe.mp hstamp

/-! ## Confirmation acceptance timing -/

/-- A support cutoff is a public tick time. -/
theorem publicTime_support_cutoff (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.support_cutoff S.E s) :=
  (publicTime_iff S _).mpr ⟨s, Or.inr (Or.inr (Or.inl rfl))⟩

/-- A Goldfish view freeze is a public tick time. -/
theorem publicTime_view_freeze (S : Setup V) (s : Slot) :
    PublicTime S (Protocol.view_freeze S.E s) :=
  (publicTime_iff S _).mpr ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩

/-- In an admissible run, `ConfirmationAcceptanceTiming` holds for every honest `v` and slot `s`. -/
theorem confirmationAcceptanceTiming_of_admissible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot) :
    ConfirmationAcceptanceTiming S rho v s := by
  intro u hu i t hacc
  have hlo := proposal_time_le_of_acceptsAt_gfVote S adm hacc
  have hus : u.slot = s := by
    have hupool : u ∈ (Proofs.Optimistic.confStore S rho v s).pool s := by
      rw [confVotes, Finset.mem_filter, confEarly, beforeCutoff, Finset.mem_filter] at hu
      exact hu.1.1
    obtain ⟨n, hn, -⟩ :=
      Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed
        (Protocol.confirmation_time S.E s)
    have hstoreEq : Proofs.Optimistic.confStore S rho v s =
        Proofs.Optimistic.tickStore S (rho.stateBefore S n v).st.core
          (Protocol.confirmation_time S.E s) := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st (congrFun hn v)]
    have huprefix : u ∈ (rho.stateBefore S n v).st.core.pool s := by
      rw [hstoreEq] at hupool
      simpa only [Proofs.Optimistic.tickStore, Protocol.Store.pool] using hupool
    have hulist : u ∈ (rho.stateBefore S n v).st.core.gf_votes s := by
      simpa only [Protocol.Store.pool, List.mem_toFinset] using huprefix
    exact (poolStamps_stateBefore S adm.toNamedScheduleWellFormed v n).slot s u hulist
  have hhi : t < Protocol.support_cutoff S.E s := by
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v s) s :=
      (Finset.mem_filter.mp hu).1
    rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
    have hreceipt := Protocol.stampedBefore_of_resolution hearly.2
    obtain ⟨n, hn, -⟩ :=
      Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed
        (Protocol.confirmation_time S.E s)
    have hstoreEq : Proofs.Optimistic.confStore S rho v s =
        Proofs.Optimistic.tickStore S (rho.stateBefore S n v).st.core
          (Protocol.confirmation_time S.E s) := by
      unfold Proofs.Optimistic.confStore Run.storeBeforeTime
      rw [congrArg NamedNodeState.st (congrFun hn v)]
    have hstamp : stampedBefore (rho.stateBefore S n v).st.core.timestamp_vote
        (Protocol.support_cutoff S.E s) u = true := by
      rw [hstoreEq] at hreceipt
      simpa only [Proofs.Optimistic.tickStore] using hreceipt
    have hi : i < n := by
      by_contra hnot
      have hni : n ≤ i := Nat.le_of_not_gt hnot
      have hisSome : ((rho.stateBefore S n v).st.core.timestamp_vote u).isSome = true := by
        cases hc : (rho.stateBefore S n v).st.core.timestamp_vote u with
        | none =>
            rw [stampedBefore, hc] at hstamp
            simp at hstamp
        | some c => simp only [Option.isSome_some]
      have hnmem : u ∈ (rho.stateBefore S n v).st.core.gf_votes u.slot :=
        (poolStamps_stateBefore S adm.toNamedScheduleWellFormed v n).pooled u hisSome
      have hcarry : PoolCarry (rho.stateBefore S n v).st.core
          (rho.stateBefore S i v).st.core :=
        pool_carry S adm.toNamedScheduleWellFormed v i hni
      have himem := hcarry.mem u.slot u hnmem
      have hpre : u ∉ (rho.stateBefore S i v).st.core.gf_votes u.slot := by
        simpa only [Object.processed, NamedReceipt.processed, decide_eq_false_iff_not,
          Protocol.Store.pool, List.mem_toFinset] using hacc.2.1
      exact hpre himem
    exact acceptsAt_gfVote_lt_of_stamp_before S adm hv hacc
      (Nat.succ_le_of_lt hi) (publicTime_support_cutoff S s) hstamp
  rw [hus] at hlo
  exact ⟨hlo, hhi⟩

/-- In an admissible run, `ConfirmationVotesAcceptedInWindow` holds for every honest `v`'s
    confirmation store at slot `s`. -/
theorem confirmationVotesAcceptedInWindow_of_admissible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (s : Slot) :
    ConfirmationVotesAcceptedInWindow S rho v
      (Proofs.Optimistic.confStore S rho v s) s :=
  confirmationVotesAcceptedInWindow_of_timing S adm
    (confirmationAcceptanceTiming_of_admissible S adm hv s)

/-- In an admissible run, `TargetReceiptVotesAcceptedInWindow` holds for every honest `w` and slot
    `s`. -/
theorem targetReceiptVotesAcceptedInWindow_of_admissible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (s : Slot) :
    TargetReceiptVotesAcceptedInWindow S rho w s := by
  intro u hu
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
  have hstoreEq : Proofs.Optimistic.voteDutyStore S rho w (s + 1) =
      Proofs.Optimistic.voteStore S (rho.stateBefore S n w).st.core (s + 1) := by
    unfold Proofs.Optimistic.voteDutyStore Run.storeBeforeTime
    rw [congrArg NamedNodeState.st (congrFun hn w)]
  have huPrefix : u ∈ beforeCutoff
      (rho.stateBefore S n w).st.core.timestamp_vote
      (Protocol.view_freeze S.E s)
      ((rho.stateBefore S n w).st.core.pool s) := by
    rw [hstoreEq] at hu
    simpa only [Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Protocol.Store.pool] using hu
  have huPool : u ∈ (rho.stateBefore S n w).st.core.pool s :=
    (Finset.mem_filter.mp huPrefix).1
  have huList : u ∈ (rho.stateBefore S n w).st.core.gf_votes s := by
    simpa only [Protocol.Store.pool, List.mem_toFinset] using huPool
  have hus : u.slot = s :=
    (poolStamps_stateBefore S adm.toNamedScheduleWellFormed w n).slot s u huList
  have hprocessed : Object.processed (rho.stateBefore S n w).st (Object.gfVote u) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    rw [hus]
    exact huPool
  obtain ⟨i, hin, t, hacc⟩ :=
    acceptsAt_gfVote_of_processed S rho w n u hprocessed
  have hlo : Protocol.proposal_time S.E s ≤ t := by
    rw [← hus]
    exact proposal_time_le_of_acceptsAt_gfVote S adm hacc
  have hhi : t < Protocol.view_freeze S.E s := by
    apply acceptsAt_gfVote_lt_of_stamp_before S adm hw hacc
      (Nat.succ_le_of_lt hin) (publicTime_view_freeze S s)
    exact (Finset.mem_filter.mp huPrefix).2
  exact ⟨i, t, hacc, hus, hlo, hhi⟩


namespace WeakExecution

end WeakExecution

end Protocol
end DecoupledConsensusModel

end
