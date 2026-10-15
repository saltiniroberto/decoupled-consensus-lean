module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Admissible
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
import Proofs.Vocabulary.Protocol.Handlers.TickBridges
import Mathlib.Tactic.ENatToNat

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# One Goldfish vote per honest validator per slot

An honest validator emits at most one Goldfish vote per slot, at that slot's vote time. The file
also holds the slot facts of the store handlers, the head-arrival condition `HeadArrivesBefore`, and
`SgRounds`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## One Goldfish vote per tick -/

omit [Fintype V] in
/-- `update_finality` leaves the slot unchanged. -/
theorem update_finality_slot (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).s = st.s := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `on_goldfish_vote` leaves the slot unchanged. -/
theorem on_goldfish_vote_slot (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).s = st.s := by
  unfold Protocol.on_goldfish_vote
  split_ifs <;> rfl

/-- `on_goldfish_vote_checked` leaves the slot unchanged. -/
theorem on_goldfish_vote_checked_slot (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).s = st.s := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_slot st u
  · rfl


/-- Folding `on_goldfish_vote_checked` leaves the slot unchanged. -/
theorem foldl_on_goldfish_vote_checked_slot (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).s = st.s := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_slot]

omit [Fintype V] in
/-- `on_sg_vote` leaves the slot unchanged. -/
theorem on_sg_vote_slot (hc : HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).s = st.s := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

private theorem named_tick_computed_duties (gc : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedTick.tick gc E hc cfg nd st record t =
      let s := E.slotOf t
      let st0 := Protocol.NamedStore.setClock E st t
      let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
      let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      let st1 := if proposalDue then proposed.1 else st0
      let emitted1 := if proposalDue then
        match proposed.2 with
        | none => []
        | some B => [Object.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map Object.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [Object.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 named_tick_computed_duties.match_1
  rfl

/-- The emission list of `on_tick_emit` is the scheduler's own. -/
private theorem on_tick_emit_snd_eq (S : Setup V) (v : V) (n : NodeState V) (t : Time) :
    (on_tick_emit S v n t).2 =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl


/-- A vote returned by `goldfish_vote_with` has the node's index as voter and the store's slot. -/
theorem goldfish_vote_with_snd (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) {u : GoldfishVote V}
    (h : (Protocol.goldfish_vote_with contract E hc nd st).2 = some u) :
    u.val_index = nd.val_index ∧ u.slot = st.s := by
  simp only [Protocol.goldfish_vote_with] at h
  split_ifs at h
  rw [← Option.some_inj.mp h]
  exact ⟨rfl, rfl⟩

/-- A Goldfish vote `u` emitted by `v`'s tick at `t` has voter `v` and slot `E.slotOf t > 0`, `t` is
    that slot's vote time, and `u` is the output of the named vote duty on the tick's prepared read. -/
theorem gfVote_emitted_shape (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {u : GoldfishVote V} (h : Object.gfVote u ∈ (on_tick_emit S v n t).2) :
    0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) ∧
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract (NamedActionReads.confirmationReadFrom S n t).cache)
        S.E S.hc (S.node v) (NamedActionReads.confirmationReadFrom S n t).st).2 = some u ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t := by
  rw [on_tick_emit_snd_eq, named_tick_computed_duties] at h
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgc
  set s := S.E.slotOf t with hs
  set st0 := Protocol.NamedStore.setClock S.E n.st t with hst0
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0
    with hproposed
  set proposalDue := 0 < s ∧ t = Protocol.proposal_time S.E s ∧
    S.E.proposer s = (S.node v).val_index with hproposalDue
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  set emitted1 : List (Object V) := if proposalDue then
    (match proposed.2 with | none => [] | some B => [Object.block B]) else [] with hemitted1def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1 with hvoted
  set voteDue := 0 < s ∧ t = Protocol.vote_time S.E s with hvoteDue
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set emitted2 : List (Object V) := if voteDue then voted.2.toList.map Object.gfVote else []
    with hemitted2def
  set st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2 with hst3def
  have hb : ∀ o ∈ emitted1, ∀ w : GoldfishVote V, o ≠ Object.gfVote w := by
    rw [hemitted1def]
    split
    · split
      · simp
      · rename_i B _
        intro o ho w
        rw [List.mem_singleton] at ho
        rw [ho]; simp
    · intro o ho; simp at ho
  have hmem : Object.gfVote u ∈ emitted1 ++ emitted2 := by
    by_cases hA : t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
        (S.node v).awake (S.hc.round_of st3.core.s) = true
    · rw [if_pos hA] at h
      rcases List.mem_append.mp h with h' | h'
      · exact h'
      · exact absurd (List.mem_singleton.mp h') (by simp)
    · rw [if_neg hA] at h
      exact h
  rcases List.mem_append.mp hmem with h' | h'
  · exact absurd rfl (hb _ h' u)
  · rw [hemitted2def] at h'
    split_ifs at h' with hvd
    · obtain ⟨w, hw, hwu⟩ := List.mem_map.mp h'
      have hueq : w = u := by simpa using hwu
      subst hueq
      have hduty : voted.2 = some w := by simpa using hw
      have hpne : ¬ proposalDue := by
        rw [hproposalDue]
        rintro ⟨-, hteq, -⟩
        exact vote_time_ne_proposal_time S.E s (hvd.2.symm.trans hteq)
      have hst1eq : st1 = st0 := by rw [hst1def, if_neg hpne]
      rw [hst1eq] at hvoted
      rw [hvoted] at hduty
      have hcoreduty : (Protocol.goldfish_vote_with gc S.E S.hc (S.node v) st0.core).2 = some w :=
        hduty
      obtain ⟨hval, hslot⟩ := goldfish_vote_with_snd gc S.E S.hc (S.node v) st0.core hcoreduty
      have hslot' : w.slot = s := by rw [hslot, hst0]; rfl
      exact ⟨hvd.1, hvd.2, hduty, by rw [hval, S.node_val_index], hslot'⟩
    · exact absurd h' (by simp)

/-- A tick emits at most one Goldfish vote. -/
theorem gfVote_emitted_unique (S : Setup V) (v : V) (n : NodeState V) (t : Time)
    {u₁ u₂ : GoldfishVote V}
    (h₁ : Object.gfVote u₁ ∈ (on_tick_emit S v n t).2)
    (h₂ : Object.gfVote u₂ ∈ (on_tick_emit S v n t).2) : u₁ = u₂ := by
  obtain ⟨-, -, hd₁, -, -⟩ := gfVote_emitted_shape S v n t h₁
  obtain ⟨-, -, hd₂, -, -⟩ := gfVote_emitted_shape S v n t h₂
  rw [hd₁] at hd₂
  exact Option.some_inj.mp hd₂

/-! ## One Goldfish vote per slot along the run -/

/-- A Goldfish vote that `v` emits at `t` has voter `v` and a slot greater than 0, and `t` is that
    slot's vote time. -/
theorem emits_gfVote_shape (S : Setup V) {ρ : Run V} {v : V} {u : GoldfishVote V}
    {t : Time} (h : ρ.emits S v (Object.gfVote u) t) :
    0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) ∧
      u.val_index = v ∧ u.slot = S.E.slotOf t := by
  obtain ⟨i, -, ho⟩ := h
  obtain ⟨hpos, ht, -, hval, hslot⟩ := gfVote_emitted_shape S v (ρ.stateBefore S i v) t ho
  exact ⟨hpos, ht, hval, hslot⟩

/-- Two Goldfish votes of the same slot emitted by `v` are equal. -/
theorem emits_gfVote_unique (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {v : V} {u₁ u₂ : GoldfishVote V} {t₁ t₂ : Time}
    (h₁ : ρ.emits S v (Object.gfVote u₁) t₁) (h₂ : ρ.emits S v (Object.gfVote u₂) t₂)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨-, ht₁, -, hu₁⟩ := emits_gfVote_shape S h₁
  obtain ⟨-, ht₂, -, hu₂⟩ := emits_gfVote_shape S h₂
  have hteq : t₁ = t₂ := by
    rw [ht₁, ht₂, ← hu₁, ← hu₂, hslot]
  subst hteq
  obtain ⟨i₁, hi₁, ho₁⟩ := h₁
  obtain ⟨i₂, hi₂, ho₂⟩ := h₂
  obtain ⟨hb₁, he₁⟩ := List.getElem?_eq_some_iff.mp hi₁
  obtain ⟨hb₂, he₂⟩ := List.getElem?_eq_some_iff.mp hi₂
  have hidx : i₁ = i₂ :=
    (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp (by rw [he₁, he₂])
  subst hidx
  exact gfVote_emitted_unique S v _ _ ho₁ ho₂


/-! ## The slot read by a vote's receiver -/

def SlotOfClock (E : Env V) (st : Protocol.Store V) : Prop :=
  st.s = E.slotOf st.t

/-- A time in `[vote_time E s, support_cutoff E s)` lies in slot `s`. -/
theorem slotOf_of_between (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.vote_time E s ≤ p) (hhi : p < Protocol.support_cutoff E s) :
    E.slotOf p = s := by
  have hbounds : ∀ a d q : Int, 0 < d → a + d ≤ q → q < a + 2 * d →
      0 ≤ q - a ∧ q - a < 4 * d := by
    intro a d q hd h1 h2; omega
  obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hhi
  have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
    unfold Env.t slotStart
    ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos s _ h0 h1


theorem vote_time_add_delta (E : Env V) (s : Slot) :
    Protocol.vote_time E s + E.Δ = Protocol.support_cutoff E s := by
  have h : ∀ a d : Int, a + d + d = a + 2 * d := by intro a d; ring
  exact h (E.t s) E.Δ

theorem support_cutoff_lt_view_freeze (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s < Protocol.view_freeze E s := by
  have h : ∀ a d : Int, 0 < d → a + 2 * d < a + 3 * d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos


/-- The block `u` names as its head is found in `T` and stamped in `tb` before `Γ`. -/
def HeadArrivesBefore (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (Γ : Time) (u : GoldfishVote V) : Prop :=
  ∃ H : Block V, Block.find? T u.head = some H ∧ stampedBefore tb Γ H = true

omit [Fintype V] in
/-- A vote `u` stamped before `Γ` whose head `H` is found in `T`, has slot at most `u`'s and is
    stamped before `Γ`, is also before `Γ` under the resolution time. -/
theorem mem_tau_cutoff_of {T : Finset (Block V)} {tb : TimestampMap (Block V)}
    {tv : TimestampMap (GoldfishVote V)} {S' : Finset (GoldfishVote V)}
    {u : GoldfishVote V} {H : Block V} {Γ : Time}
    (hmem : u ∈ beforeCutoff tv Γ S') (hfind : Block.find? T u.head = some H)
    (hslot : H.slot ≤ u.slot)
    (hH : stampedBefore tb Γ H = true) :
    u ∈ beforeCutoff (Protocol.resolution_time T tb tv) Γ S' := by
  rw [beforeCutoff, Finset.mem_filter] at hmem ⊢
  exact ⟨hmem.1, Protocol.stampedBefore_resolution_of hfind hslot hmem.2 hH⟩

/-! ## Proposal votes and SG rounds -/


/-- The Goldfish votes of a block the named proposal duty returns are the store's votes of slot
    `st.core.s - 1`. -/
theorem proposal_with_gf_votes (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) {B : NamedBlock V}
    (hB : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    B.gf_votes = st.core.gf_votes (st.core.s - 1) := by
  simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
    Option.map_eq_some_iff] at hB
  obtain ⟨parent, -, hBeq⟩ := hB
  rw [← hBeq]
  rfl

/-- A block the named proposal duty returns has the store's slot. -/
theorem proposal_with_slot (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) {B : NamedBlock V}
    (hB : Protocol.NamedActions.proposal_with contract source E hc nd st = some B) :
    B.slot = st.core.s := by
  simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
    Option.map_eq_some_iff] at hB
  obtain ⟨parent, -, hBeq⟩ := hB
  rw [← hBeq]
  rfl


/-- `sg_votes r` holds round-`r` attestations only. -/
def SgRounds (st : Protocol.Store V) : Prop :=
  ∀ (r : Round) (a : CombinedAttestation V), a ∈ st.sg_votes r → a.round = r


omit [Fintype V] in
/-- `x` is in `round_votes st a` exactly when the SG pool of `a`'s round holds an attestation by
    `a`'s voter with confirmed value `x`. -/
theorem mem_round_votes {st : Protocol.Store V} {a : CombinedAttestation V}
    {x : Option BlockId} :
    x ∈ Protocol.round_votes st a ↔
      ∃ b ∈ st.sg_pool a.round, b.val_index = a.val_index ∧ b.confirmed = x := by
  simp [Protocol.round_votes, and_assoc]


end Optimistic
end Proofs
end DecoupledConsensusModel

end
