module
public import Proofs.Vocabulary.Protocol.Handlers.Invariants
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

/-!
# Block storage and stamps

Block membership and block stamps have the same domain at every state of a run, a block stamp is
never rewritten, and a block and its stamp carry to every later state.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Block facts of one store -/

/-- The block tree and the block stamps have the same domain, and every stamp is at or before the
    store clock. -/
structure BlockStamps (st : Protocol.Store V) : Prop where
  /-- Every tree member has a block stamp. -/
  stamped : ∀ B : Block V, B ∈ st.T → (st.timestamp_block B).isSome = true
  /-- Every block stamp belongs to a tree member. -/
  stored : ∀ B : Block V, (st.timestamp_block B).isSome = true → B ∈ st.T
  /-- Every block stamp is at or before the store clock. -/
  bounded : ∀ (B : Block V) (c : Stamp), st.timestamp_block B = some c →
    c ≤ (st.t : Stamp)

/-- What carries from one block store to a later one. -/
structure BlockCarry (st st' : Protocol.Store V) : Prop where
  /-- The tree only grows. -/
  mem : ∀ B : Block V, B ∈ st.T → B ∈ st'.T
  /-- A written block stamp is never rewritten. -/
  stamp : ∀ (B : Block V) (c : Stamp), st.timestamp_block B = some c →
    st'.timestamp_block B = some c

/-- One transition carries old blocks and stamps and preserves `BlockStamps`. -/
def BlockStep (st st' : Protocol.Store V) : Prop :=
  BlockStamps st → BlockCarry st st' ∧ BlockStamps st'

namespace BlockStep

variable {st st' st'' : Protocol.Store V}

omit [DecidableEq V] [Fintype V] in
/-- `BlockStep` is reflexive. -/
theorem refl' (st : Protocol.Store V) : BlockStep st st :=
  fun h => ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, h⟩

omit [DecidableEq V] [Fintype V] in
/-- `BlockStep` is transitive. -/
theorem trans' (h₁ : BlockStep st st') (h₂ : BlockStep st' st'') :
    BlockStep st st'' := by
  intro hs
  obtain ⟨hc₁, hs'⟩ := h₁ hs
  obtain ⟨hc₂, hs''⟩ := h₂ hs'
  exact ⟨⟨fun B hB => hc₂.mem B (hc₁.mem B hB),
    fun B c hc => hc₂.stamp B c (hc₁.stamp B c hc)⟩, hs''⟩

omit [DecidableEq V] [Fintype V] in
/-- A step that keeps the tree, the block stamps and the clock is a `BlockStep`. -/
theorem of_eq (hT : st'.T = st.T)
    (htb : st'.timestamp_block = st.timestamp_block) (ht : st'.t = st.t) :
    BlockStep st st' := by
  intro hs
  refine ⟨⟨fun B hB => by rw [hT]; exact hB,
      fun B c hc => by rw [htb]; exact hc⟩, ?_⟩
  exact ⟨fun B hB => by rw [htb]; exact hs.stamped B (by rwa [hT] at hB),
    fun B hB => by rw [hT]; exact hs.stored B (by rwa [htb] at hB),
    fun B c hc => by rw [ht]; exact hs.bounded B c (by rwa [htb] at hc)⟩

end BlockStep

/-! ## Handler preservation -/

omit [Fintype V] in
/-- `update_finality` preserves the block timestamp map. -/
theorem update_finality_timestamp_block (st : Protocol.Store V)
    (σ : Protocol.ChainState V) :
    (Protocol.update_finality st σ).timestamp_block = st.timestamp_block := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` preserves the block timestamp map. -/
theorem on_goldfish_vote_timestamp_block (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).timestamp_block = st.timestamp_block := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` preserves the block timestamp map. -/
theorem on_goldfish_vote_checked_timestamp_block (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).timestamp_block =
      st.timestamp_block := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_timestamp_block st u
  · rfl


/-- A fold of `on_goldfish_vote_checked` preserves the block timestamp map. -/
theorem foldl_on_goldfish_vote_checked_timestamp_block (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).timestamp_block =
      st.timestamp_block := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_timestamp_block]

omit [Fintype V] in
/-- `on_sg_vote` preserves the block timestamp map. -/
theorem on_sg_vote_timestamp_block (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    (Protocol.on_sg_vote hc st a).timestamp_block = st.timestamp_block := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-- Setting the clock to a later time `t` is a `BlockStep`. -/
theorem blockStep_tick_store (E : Env V) (st : Protocol.Store V) (t : Time)
    (ht : st.t ≤ t) : BlockStep st (tick_store E st t) := by
  intro hs
  refine ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, ?_⟩
  exact ⟨hs.stamped, hs.stored, fun B c hc =>
    le_trans (hs.bounded B c hc) (by exact_mod_cast ht)⟩


/-- `on_goldfish_vote_checked` is a `BlockStep`. -/
theorem blockStep_on_goldfish_vote_checked (E : Env V)
    (st : Protocol.Store V) (u : GoldfishVote V) :
    BlockStep st (Protocol.on_goldfish_vote_checked E st u) :=
  BlockStep.of_eq (Proofs.on_goldfish_vote_checked_T E st u)
    (on_goldfish_vote_checked_timestamp_block E st u)
    (on_goldfish_vote_checked_time E st u)

omit [Fintype V] in
/-- `on_sg_vote` is a `BlockStep`. -/
theorem blockStep_on_sg_vote (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : BlockStep st (Protocol.on_sg_vote hc st a) :=
  BlockStep.of_eq (Proofs.on_sg_vote_T hc st a)
    (on_sg_vote_timestamp_block hc st a) (on_sg_vote_time hc st a)


/-- `on_block_using` is a `BlockStep`, whatever chain state it builds. -/
theorem blockStep_on_block_using (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    BlockStep st (Protocol.on_block_using E st B buildState) := by
  intro hs
  by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_pos hfirst]]
    exact ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, hs⟩
  by_cases hadmit : (!Block.preceq st.F B) = true
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_neg hfirst, if_pos hadmit]]
    exact ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, hs⟩
  by_cases hprop : B.proposer? ≠ some (E.proposer B.slot)
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_neg hfirst, if_neg hadmit, if_pos hprop]]
    exact ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, hs⟩
  by_cases hslot : ¬ B.parent.slot < B.slot
  · rw [show Protocol.on_block_using E st B buildState = st by
      simp only [Protocol.on_block_using, if_neg hfirst, if_neg hadmit, if_neg hprop,
        if_pos hslot]]
    exact ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, hs⟩
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
  have hBnot : B ∉ st.T := fun hB => hfirst (Or.inr (Or.inl hB))
  have hTu : unpacked.T = insert B st.T := by
    simp only [unpacked, Proofs.foldl_on_goldfish_vote_checked_T, stored]
  have htbu : unpacked.timestamp_block =
      (fun C => if C = B then some (st.t : Stamp) else st.timestamp_block C) := by
    simp only [unpacked, foldl_on_goldfish_vote_checked_timestamp_block, stored]
  have hTout : (Protocol.on_block_using E st B buildState).T = insert B st.T := by
    rw [hout, Proofs.update_finality_T, hTu]
  have htbout : (Protocol.on_block_using E st B buildState).timestamp_block =
      (fun C => if C = B then some (st.t : Stamp) else st.timestamp_block C) := by
    rw [hout, update_finality_timestamp_block, htbu]
  have htout : (Protocol.on_block_using E st B buildState).t = st.t :=
    on_block_using_time E st B buildState
  refine ⟨?_, ?_⟩
  · refine ⟨fun C hC => by rw [hTout]; exact Finset.mem_insert_of_mem hC,
      fun C c hc => ?_⟩
    rw [htbout]
    by_cases hCB : C = B
    · subst C
      exfalso
      have hmem : B ∈ st.T := hs.stored B (by rw [hc]; simp)
      exact hBnot hmem
    · simpa [hCB] using hc
  · refine ⟨?_, ?_, ?_⟩
    · intro C hC
      rw [hTout] at hC
      rw [htbout]
      rcases Finset.mem_insert.mp hC with rfl | hC
      · simp
      · by_cases hCB : C = B
        · subst C; exact absurd hC hBnot
        · simpa [hCB] using hs.stamped C hC
    · intro C hC
      rw [htbout] at hC
      rw [hTout]
      by_cases hCB : C = B
      · subst C
        exact Finset.mem_insert_self _ _
      · simp only [hCB, ↓reduceIte] at hC
        exact Finset.mem_insert_of_mem (hs.stored C hC)
    · intro C c hc
      rw [htbout] at hc
      rw [htout]
      by_cases hCB : C = B
      · subst C
        simp only [↓reduceIte, Option.some.injEq] at hc
        exact le_of_eq hc.symm
      · exact hs.bounded C c (by simpa [hCB] using hc)

omit [DecidableEq V] [Fintype V] in
/-- The checked wrapper `on_block_checked_using` around a handler that is a `BlockStep` is a
    `BlockStep`. -/
theorem blockStep_on_block_checked_using (handle : Protocol.Store V → Protocol.Store V)
    (hc : HealConfig) (st : Protocol.Store V) (B : Block V)
    (hh : BlockStep st (handle st)) :
    BlockStep st (Protocol.on_block_checked_using handle hc st B) := by
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · rw [show Protocol.on_block_checked_using handle hc st B = handle st by
      simp [Protocol.on_block_checked_using, hvalid]]
    exact hh
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    rw [show Protocol.on_block_checked_using handle hc st B = st by
      simp [Protocol.on_block_checked_using, hfalse]]
    exact BlockStep.refl' st

/-- The Goldfish vote duty `goldfish_vote_with` is a `BlockStep`, for every grade contract. -/
theorem blockStep_goldfish_vote_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    BlockStep st (Protocol.goldfish_vote_with contract E hc nd st).1 := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact blockStep_on_goldfish_vote_checked E st _
  · exact BlockStep.refl' st

/-- The Goldfish vote duty `goldfish_vote_with` leaves the block tree unchanged. -/
theorem goldfish_vote_with_T (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1.T = st.T := by
  simp only [Protocol.goldfish_vote_with, Protocol.on_goldfish_vote_checked,
    Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- The confirmation duty `update_confirmation_with` is a `BlockStep`, for every grade contract. -/
theorem blockStep_update_confirmation_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.Store V) (s : Slot) :
    BlockStep st (Protocol.update_confirmation_with contract E hc st s) :=
  BlockStep.of_eq rfl rfl rfl

/-! ### The named block handler and row admission -/

/-- The core of `process_block_core` is a `BlockStep`. -/
theorem blockStep_process_block_core (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    BlockStep st.core (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  by_cases hp : B.parent ∉ st.bodies
  · rw [show Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B = st by
      simp only [Protocol.NamedStore.process_block_core, if_pos hp]]
    exact BlockStep.refl' st.core
  · rw [show Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B =
        Protocol.NamedStore.commitBlock st
          (Protocol.on_block_checked_using
            (fun current => Protocol.on_block_using S.E current B.erase
              (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
            S.hc st.core B.erase) B by
      simp only [Protocol.NamedStore.process_block_core, if_neg hp]]
    rw [commitBlock_core]
    exact blockStep_on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase (blockStep_on_block_using S.E st.core B.erase _)

omit [Fintype V] in
/-- The core of `admit_row` is a `BlockStep`. -/
theorem blockStep_admit_row (hc : HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    BlockStep st.core (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [admit_row_core]
  exact blockStep_on_sg_vote hc st.core a.erase

omit [Fintype V] in
/-- `admit_row` leaves the bodies unchanged. -/
theorem admit_row_bodies (hc : HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).bodies = st.bodies := by
  simp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `admit_row` leaves the core tree unchanged. -/
theorem admit_row_core_T (hc : HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core.T = st.core.T := by
  rw [admit_row_core]
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl


/-- The core of `admit_rows` is a `BlockStep`. -/
theorem blockStep_admit_rows (hc : HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    BlockStep st.core (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact BlockStep.refl' st.core
  | cons a rows ih =>
      have heq : Protocol.NamedAdmission.admit_rows hc st (a :: rows) =
          Protocol.NamedAdmission.admit_rows hc (Protocol.NamedAdmission.admit_row hc st a) rows :=
        rfl
      rw [heq]
      exact BlockStep.trans' (blockStep_admit_row hc st a) (ih _)

omit [Fintype V] in

/-- `admit_rows` leaves the bodies and the core tree unchanged. -/
theorem admit_rows_bodies_and_core_T (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies ∧
        (Protocol.NamedAdmission.admit_rows hc st rows).core.T = st.core.T := by
  intro rows
  induction rows with
  | nil => intro st; exact ⟨rfl, rfl⟩
  | cons a rows ih =>
      intro st
      have heq : Protocol.NamedAdmission.admit_rows hc st (a :: rows) =
          Protocol.NamedAdmission.admit_rows hc (Protocol.NamedAdmission.admit_row hc st a) rows :=
        rfl
      rw [heq]
      obtain ⟨hb, ht⟩ := ih (Protocol.NamedAdmission.admit_row hc st a)
      exact ⟨hb.trans (admit_row_bodies hc st a), ht.trans (admit_row_core_T hc st a)⟩

/-- The core of `admit_carried` is a `BlockStep`. -/
theorem blockStep_admit_carried (adm : Protocol.CarriedAdmission) (hc : HealConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    BlockStep after.core (Protocol.NamedAdmission.admit_carried adm hc before after B).core := by
  cases adm with
  | alsoCarried =>
      unfold Protocol.NamedAdmission.admit_carried
      split_ifs
      · exact blockStep_admit_rows hc after B.attestations
      · exact BlockStep.refl' after.core

/-- The core of `on_block_with` is a `BlockStep`, for either carried-row policy. -/
theorem blockStep_on_block_with (adm : Protocol.CarriedAdmission) (S : Setup V)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    BlockStep st.core (Protocol.NamedAdmission.on_block_with adm S.E S.hc S.cfg st B).core := by
  unfold Protocol.NamedAdmission.on_block_with
  exact BlockStep.trans' (blockStep_process_block_core S st B)
    (blockStep_admit_carried adm S.hc st
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) B)

/-! ### The four named duties -/

theorem blockStep_named_propose_block_with (contract : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    BlockStep st.core
      (Protocol.NamedDuties.propose_block_with contract S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact BlockStep.refl' st.core
  · exact blockStep_on_block_with .alsoCarried S st _

theorem blockStep_named_goldfish_vote_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    BlockStep st.core (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core :=
  blockStep_goldfish_vote_with contract E hc nd st.core

theorem blockStep_named_update_confirmation_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    BlockStep st.core
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core :=
  blockStep_update_confirmation_with contract E hc st.core s

theorem blockStep_named_attest_with (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    BlockStep st.core
      (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core :=
  blockStep_admit_row hc st _

/-- A named tick to a time `t` not earlier than the store's clock is a `BlockStep` on the core, for
    every grade contract. -/
theorem blockStep_named_tick (gc : Protocol.GradeContract V) (S : Setup V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hle : st.core.t ≤ t) :
    BlockStep st.core (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  have h0 : BlockStep st.core (Protocol.NamedStore.setClock S.E st t).core :=
    blockStep_tick_store S.E st.core t hle
  exact named_tick_preserves (fun st' => BlockStep st.core st'.core) gc S.E S.hc S.cfg nd
    (fun st' h => BlockStep.trans' h (blockStep_named_propose_block_with gc S nd st'))
    (fun st' h => BlockStep.trans' h (blockStep_named_goldfish_vote_with gc S.E S.hc nd st'))
    (fun st' s h =>
      BlockStep.trans' h (blockStep_named_update_confirmation_with gc S.E S.hc st' s))
    (fun st' record' h =>
      BlockStep.trans' h (blockStep_named_attest_with gc S.E S.hc nd st' record'))
    st record t h0

/-- An emitting tick to a time not earlier than the store's clock is a `BlockStep` on the core. -/
theorem blockStep_on_tick_emit (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    (hle : n.st.core.t ≤ t) : BlockStep n.st.core (on_tick_emit S v n t).1.st.core := by
  simp only [on_tick_emit, NamedNode.tick, NamedProfile.tick]
  exact blockStep_named_tick _ S (S.node v) n.st n.record t hle

/-- Processing a delivered object is a `BlockStep` on the core. -/
theorem blockStep_process (S : Setup V) (n : NodeState V) (o : Object V) :
    BlockStep n.st.core (n.process S o).st.core := by
  cases o with
  | block B =>
      show BlockStep n.st.core
        (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg n.st B).core
      exact blockStep_on_block_with .alsoCarried S n.st B
  | gfVote u =>
      show BlockStep n.st.core
        ({ n.st with core := Protocol.on_goldfish_vote_checked S.E n.st.core u } :
          Protocol.NamedStore V).core
      exact blockStep_on_goldfish_vote_checked S.E n.st.core u
  | attest a =>
      show BlockStep n.st.core (Protocol.NamedAdmission.admit_row S.hc n.st a).core
      exact blockStep_admit_row S.hc n.st a

/-! ## Preservation along a run -/

omit [Fintype V] in
/-- The initial core tree contains only genesis, whose stamp is `⊥`. -/
theorem blockStamps_init :
    BlockStamps (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Protocol.NamedStore.initial, Protocol.Store.init, genesisStamp]

/-- The store clock before an indexed event is no later than the event time. -/
theorem block_store_time_le_event_time (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {n : Nat} {e : Event V}
    (he : ρ.events[n]? = some e) (v : V) :
    (ρ.stateBefore S n v).st.core.t ≤ e.time := by
  rw [store_time_eq_lastTick]
  cases hl : Run.lastTickIn v (ρ.events.take n) with
  | none =>
      simpa using (sch.in_horizon _ (List.mem_of_getElem? he)).1
  | some p =>
      have hmem : Event.tick v p ∈ ρ.events.take n :=
        tick_mem_of_lastTickIn v _ hl
      simpa [Event.time, NamedEvent.time] using time_le_of_mem_take S sch he _ hmem

/-- After one indexed event, every store clock is still no later than that
event. -/
theorem block_store_time_after_event_le (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {n : Nat} {e : Event V}
    (he : ρ.events[n]? = some e) (v : V) :
    (ρ.stateBefore S (n + 1) v).st.core.t ≤ e.time := by
  have hstep : ρ.stateBefore S (n + 1) =
      (ρ.events[n]?.toList).foldl (World.step S) (ρ.stateBefore S n) := by
    unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, List.foldl_append]
  have hbefore := block_store_time_le_event_time S sch he v
  cases e with
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        have heq : ρ.stateBefore S (n + 1) v =
            Execution.NamedNode.process S (ρ.stateBefore S n v) o := by
          rw [hstep, he]
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_self]
        rw [heq, (process_time S (ρ.stateBefore S n v) o).1]
        exact hbefore
      · have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
          rw [hstep, he]
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_of_ne (Ne.symm hu)]
        rw [heq]
        exact hbefore
  | tick u t =>
      by_cases hu : u = v
      · subst u
        have heq : ρ.stateBefore S (n + 1) v =
            (on_tick_emit S v (ρ.stateBefore S n v) t).1 := by
          rw [hstep, he]
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_self]
        rw [heq]
        exact le_of_eq (on_tick_emit_time S v (ρ.stateBefore S n v) t).1
      · have heq : ρ.stateBefore S (n + 1) v = ρ.stateBefore S n v := by
          rw [hstep, he]
          simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step, NamedWorld.step,
            Function.update_of_ne (Ne.symm hu)]
        rw [heq]
        exact hbefore

/-- Every indexed event is a `BlockStep` on every node's core. -/
theorem blockStep_event (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {n : Nat} {e : Event V}
    (he : ρ.events[n]? = some e) (v : V) :
    BlockStep (ρ.stateBefore S n v).st.core
      ((World.step S (ρ.stateBefore S n) e v).st.core) := by
  cases e with
  | deliver u o t =>
      by_cases hu : u = v
      · subst u
        have heq : World.step S (ρ.stateBefore S n) (Event.deliver v o t) v =
            Execution.NamedNode.process S (ρ.stateBefore S n v) o := by
          simp only [World.step, NamedWorld.step, Function.update_self]
        rw [heq]
        exact blockStep_process S (ρ.stateBefore S n v) o
      · have heq : World.step S (ρ.stateBefore S n) (Event.deliver u o t) v =
            ρ.stateBefore S n v := by
          simp only [World.step, NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        rw [heq]
        exact BlockStep.refl' _
  | tick u t =>
      by_cases hu : u = v
      · subst u
        have heq : World.step S (ρ.stateBefore S n) (Event.tick v t) v =
            (on_tick_emit S v (ρ.stateBefore S n v) t).1 := by
          simp only [World.step, NamedWorld.step, Function.update_self]
        rw [heq]
        refine blockStep_on_tick_emit S v _ t ?_
        simpa [Event.time, NamedEvent.time] using block_store_time_le_event_time S sch he v
      · have heq : World.step S (ρ.stateBefore S n) (Event.tick u t) v =
            ρ.stateBefore S n v := by
          simp only [World.step, NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        rw [heq]
        exact BlockStep.refl' _

/-- At every state of a run, every node's core store satisfies `BlockStamps`. -/
theorem blockStamps_stateBefore (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (v : V) :
    ∀ n : Nat, BlockStamps (ρ.stateBefore S n v).st.core := by
  intro n
  induction n with
  | zero =>
      simpa [Run.stateBefore, NamedRun.stateBefore, World.init, NamedWorld.init,
        NamedNode.initial] using blockStamps_init (V := V)
  | succ n ih =>
      have hstep : ρ.stateBefore S (n + 1) =
          (ρ.events[n]?.toList).foldl (World.step S) (ρ.stateBefore S n) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases he : ρ.events[n]? with _ | e
      · rw [hstep, he]
        exact ih
      · have hworld : ρ.stateBefore S (n + 1) v =
            World.step S (ρ.stateBefore S n) e v := by
          rw [hstep, he]
          simp only [Option.toList, List.foldl_cons, List.foldl_nil]
        rw [hworld]
        exact (blockStep_event S sch he v ih).2

/-- A node's blocks and their stamps carry from every state of a run to every later state. -/
theorem block_carry (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    (v : V) {m : Nat} : ∀ n : Nat, m ≤ n →
      BlockCarry (ρ.stateBefore S m v).st.core (ρ.stateBefore S n v).st.core := by
  intro n
  induction n with
  | zero =>
      intro hle
      rw [Nat.le_zero.mp hle]
      exact ⟨fun _ hB => hB, fun _ _ hc => hc⟩
  | succ n ih =>
      intro hle
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have hcarry := ih hmn
        have hstep : ρ.stateBefore S (n + 1) =
            (ρ.events[n]?.toList).foldl (World.step S) (ρ.stateBefore S n) := by
          unfold Run.stateBefore NamedRun.stateBefore
          rw [List.take_add_one, List.foldl_append]
        have hnext : BlockCarry (ρ.stateBefore S n v).st.core
            (ρ.stateBefore S (n + 1) v).st.core := by
          rcases he : ρ.events[n]? with _ | e
          · rw [hstep, he]
            exact ⟨fun _ hB => hB, fun _ _ hc => hc⟩
          · have hworld : ρ.stateBefore S (n + 1) v =
                World.step S (ρ.stateBefore S n) e v := by
              rw [hstep, he]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            rw [hworld]
            exact (blockStep_event S sch he v
              (blockStamps_stateBefore S sch v n)).1
        exact ⟨fun B hB => hnext.mem B (hcarry.mem B hB),
          fun B c hc => hnext.stamp B c (hcarry.stamp B c hc)⟩
      · rw [Nat.le_antisymm hle hge]
        exact ⟨fun _ hB => hB, fun _ _ hc => hc⟩

/-! ## Admission before a strict read -/

/-- `v` accepts a named body of `B` at an event of time before `Γ`. -/
def AdmittedBefore (S : Setup V) (ρ : Run V) (v : V) (B : Block V)
    (Γ : Time) : Prop :=
  ∃ C : NamedBlock V, C.erase = B ∧
    ∃ (i : Nat) (t : Time), NamedRun.acceptsAt S ρ i v (Object.block C) t ∧ t < Γ


/-- A named body newly present after `on_block_with` is the block the call was made with, and its
    erasure is in the resulting core tree. -/
theorem on_block_with_new_body (adm : Protocol.CarriedAdmission) (S : Setup V)
    (before : Protocol.NamedStore V) (B' C : NamedBlock V) (hpre : C ∉ before.bodies)
    (hpost : C ∈ (Protocol.NamedAdmission.on_block_with adm S.E S.hc S.cfg before B').bodies) :
    C = B' ∧
      C.erase ∈ (Protocol.NamedAdmission.on_block_with adm S.E S.hc S.cfg before B').core.T := by
  set core := Protocol.NamedStore.process_block_core S.E S.hc S.cfg before B' with hcoredef
  have hwrap : (Protocol.NamedAdmission.on_block_with adm S.E S.hc S.cfg before B').bodies =
        core.bodies ∧
      (Protocol.NamedAdmission.on_block_with adm S.E S.hc S.cfg before B').core.T =
        core.core.T := by
    unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
    cases adm with
    | alsoCarried =>
        split_ifs
        · exact admit_rows_bodies_and_core_T S.hc B'.attestations core
        · exact ⟨rfl, rfl⟩
  have hcorepost : C ∈ core.bodies := hwrap.1 ▸ hpost
  have hprebody : B'.parent ∈ before.bodies := by
    by_contra hcon
    have hcoreeq : core = before := by
      rw [hcoredef]
      unfold Protocol.NamedStore.process_block_core
      rw [if_pos hcon]
    exact hpre (hcoreeq ▸ hcorepost)
  have hcorecall : core = Protocol.NamedStore.commitBlock before
      (Protocol.on_block_checked_using
        (fun current => Protocol.on_block_using S.E current B'.erase
          (fun parentState => Protocol.named_transition S.E S.cfg parentState B'))
        S.hc before.core B'.erase) B' := by
    rw [hcoredef]
    unfold Protocol.NamedStore.process_block_core
    rw [if_neg (not_not_intro hprebody)]
  rw [hcorecall] at hcorepost
  unfold Protocol.NamedStore.commitBlock at hcorepost
  by_cases hfresh : B'.erase ∉ before.core.T ∧
      B'.erase ∈ (Protocol.on_block_checked_using
        (fun current => Protocol.on_block_using S.E current B'.erase
          (fun parentState => Protocol.named_transition S.E S.cfg parentState B'))
        S.hc before.core B'.erase).T
  · rw [if_pos hfresh] at hcorepost
    have hCeq : C = B' := by
      rcases Finset.mem_insert.mp hcorepost with h | h
      · exact h
      · exact absurd h hpre
    refine ⟨hCeq, ?_⟩
    rw [hwrap.2, hcorecall]
    unfold Protocol.NamedStore.commitBlock
    rw [if_pos hfresh, hCeq]
    exact hfresh.2
  · rw [if_neg hfresh] at hcorepost
    exact absurd hcorepost hpre

/-- After a named tick, the bodies and the core tree are those left by the tick's proposal stage. -/
theorem tick_bodies_and_coreT_from_proposal (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) :
    let s := S.E.slotOf t
    let st0 := Protocol.NamedStore.setClock S.E st t
    let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
        S.E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.bodies = st1.bodies ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core.T = st1.core.T := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have hb21 : st2.bodies = st1.bodies := by
    dsimp only [st2, Protocol.NamedDuties.goldfish_vote_with]
    split_ifs <;> rfl
  have hT21 : st2.core.T = st1.core.T := by
    dsimp only [st2, Protocol.NamedDuties.goldfish_vote_with]
    split_ifs
    · rw [show ({ st1 with core := (Protocol.goldfish_vote_with gc S.E S.hc nd st1.core).1 } :
          Protocol.NamedStore V).core.T =
          (Protocol.goldfish_vote_with gc S.E S.hc nd st1.core).1.T from rfl,
        goldfish_vote_with_T]
    · rfl
  have hb31 : st3.bodies = st1.bodies := by
    dsimp only [st3, Protocol.NamedDuties.update_confirmation_with]
    split_ifs <;> exact hb21
  have hT31 : st3.core.T = st1.core.T := by
    dsimp only [st3, Protocol.NamedDuties.update_confirmation_with]
    split_ifs <;> exact hT21
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
      Protocol.NamedTick.namedOps, Protocol.NamedStore.setClock, st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · refine ⟨?_, ?_⟩
    · rw [show (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 =
          Protocol.NamedAdmission.admit_row S.hc st3 _ from rfl, admit_row_bodies]
      exact hb31
    · rw [show (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 =
          Protocol.NamedAdmission.admit_row S.hc st3 _ from rfl, admit_row_core_T]
      exact hT31
  · exact ⟨hb31, hT31⟩

end Protocol
end DecoupledConsensusModel

end
