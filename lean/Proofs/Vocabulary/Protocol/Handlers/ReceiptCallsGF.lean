module
public import Proofs.Vocabulary.Protocol.Schedule.NamedTick
public import Proofs.Vocabulary.Protocol.Handlers.Admission
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Protocol.Handlers.Pool
public import Proofs.Vocabulary.ModelProperties.Store_pool
import Proofs.Vocabulary.Protocol.Grades.NamedDuties
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Origin of Goldfish votes in the pool

A Goldfish vote new to a validator's pool was added by an actual handler call of the named run: a
vote fold, a block call or a tick.
-/
namespace DecoupledConsensusModel.Proofs.NamedReceiptCallsGF
open Execution
open Execution.NamedReceiptCalls
variable {V : Type} [DecidableEq V] [Fintype V]


private theorem checked_new_vote_eq (E : Env V) (st : Protocol.Store V)
    (input u : GoldfishVote V) (hpre : u ∉ st.pool u.slot)
    (hpost : u ∈ (Protocol.on_goldfish_vote_checked E st input).pool u.slot) : input = u := by
  have hpost' : u ∈ (Protocol.on_goldfish_vote_checked E st input).gf_votes u.slot := by
    simpa only [Protocol.Store.pool, List.mem_toFinset] using hpost
  rcases Protocol.gfFrom_on_goldfish_vote_checked E st input u.slot u hpost' with
      hold | hin | ⟨B, hB, _⟩
  · exact False.elim (hpre (by simpa only [Protocol.Store.pool, List.mem_toFinset] using hold))
  · have he : u = input := by simpa using hin
    exact he.symm
  · simp at hB

/-- A vote new to the pool after folding `on_goldfish_vote_checked` over `rows` was added by the
    call at some index of `rows`. -/
theorem fold_new_vote_origin (E : Env V) (rows : List (GoldfishVote V))
    (st : Protocol.Store V) (u : GoldfishVote V) (hpre : u ∉ st.pool u.slot)
    (hpost : u ∈ (rows.foldl (Protocol.on_goldfish_vote_checked E) st).pool u.slot) :
    ∃ j, rows[j]? = some u ∧
      let input := (rows.take j).foldl (Protocol.on_goldfish_vote_checked E) st
      u ∉ input.pool u.slot ∧
        u ∈ (Protocol.on_goldfish_vote_checked E input u).pool u.slot := by
  induction rows generalizing st with
  | nil => exact False.elim (hpre hpost)
  | cons input rows ih =>
    by_cases hone : u ∈ (Protocol.on_goldfish_vote_checked E st input).pool u.slot
    · have he := checked_new_vote_eq E st input u hpre hone
      subst input
      exact ⟨0, by simp, by simpa using And.intro hpre hone⟩
    · obtain ⟨j, hj, hlocal⟩ := ih (Protocol.on_goldfish_vote_checked E st input) hone hpost
      refine ⟨j + 1, by simpa using hj, ?_⟩
      simpa only [List.take_succ_cons, List.foldl_cons] using hlocal

private theorem core_fresh_or_eq (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (postCore S before B).core = before.core ∨
      (B.erase ∉ before.core.T ∧ B.erase ∈ (postCore S before B).core.T) := by
  by_cases hp : B.parent ∈ before.bodies
  · simp only [postCore, Protocol.NamedStore.process_block_core,
      if_neg (not_not_intro hp), NamedStore.commit_core]
    simp only [Protocol.on_block_checked_using, Protocol.on_block_using]
    split_ifs <;> first
      | exact Or.inl rfl
      | (right
         constructor
         · intro hB
           simp_all
         · rw [Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T S.E]
           exact Finset.mem_insert_self _ _)
  · simp only [postCore, Protocol.NamedStore.process_block_core, if_pos hp]
    exact Or.inl trivial

/-- When `postCore` adds a block `B` new to the core tree, its result is built from the stored
    record `stored` of the handler's accepting branch. -/
theorem post_core_stored (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V)
    (hnew : B.erase ∉ before.core.T) (hpost : B.erase ∈ (postCore S before B).core.T) :
    let stored : Protocol.Store V := { before.core with
      σ := fun C => if C = B.erase then
        Protocol.named_transition S.E S.cfg (before.core.σ B.erase.parent) B
        else before.core.σ C
      T := insert B.erase before.core.T
      timestamp_block := fun C =>
        if C = B.erase then some (before.core.t : Stamp) else before.core.timestamp_block C }
    let unpacked := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked S.E) stored
    (postCore S before B).core = Protocol.update_finality unpacked (unpacked.σ B.erase) := by
  by_cases hp : B.parent ∈ before.bodies
  · simp only [postCore, Protocol.NamedStore.process_block_core,
      if_neg (not_not_intro hp), NamedStore.commit_core] at hpost ⊢
    dsimp only [Protocol.on_block_checked_using] at hpost ⊢
    split_ifs at hpost ⊢ <;> first
      | exact False.elim (hnew hpost)
      | (simp only [Protocol.on_block_using] at hpost ⊢
         split_ifs at hpost ⊢ <;> first
           | exact False.elim (hnew hpost)
           | (rw [Proofs.NamedWire.erase_goldfish_votes]))
  · simp only [postCore, Protocol.NamedStore.process_block_core, if_pos hp] at hpost
    exact False.elim (hnew hpost)


/-- A Goldfish vote that a block call of the run adds to the pool was added by an indexed receipt of
    that call. -/
theorem block_new_vote_origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : Protocol.NamedStore V)
    (hcall : blockCallAt S rho i v B before) (u : GoldfishVote V)
    (hpre : u ∉ before.core.pool u.slot) (hpost : u ∈ (postCore S before B).core.pool u.slot) :
    ∃ j, carriedGoldfishAt S rho i v B j u before ∧
      let stored : Protocol.Store V := { before.core with
      σ := fun C => if C = B.erase then
        Protocol.named_transition S.E S.cfg (before.core.σ B.erase.parent) B
        else before.core.σ C
      T := insert B.erase before.core.T
      timestamp_block := fun C =>
        if C = B.erase then some (before.core.t : Stamp) else before.core.timestamp_block C }
      let input := (B.gf_votes.take j).foldl (Protocol.on_goldfish_vote_checked S.E) stored
      u ∉ input.pool u.slot ∧
        u ∈ (Protocol.on_goldfish_vote_checked S.E input u).pool u.slot := by
  obtain he | ⟨hnew, hheld⟩ := core_fresh_or_eq S before B
  · rw [he] at hpost
    exact False.elim (hpre hpost)
  · let stored : Protocol.Store V := { before.core with
      σ := fun C => if C = B.erase then
        Protocol.named_transition S.E S.cfg (before.core.σ B.erase.parent) B
        else before.core.σ C
      T := insert B.erase before.core.T
      timestamp_block := fun C =>
        if C = B.erase then some (before.core.t : Stamp) else before.core.timestamp_block C }
    have hs := post_core_stored S before B hnew hheld
    have hfold : u ∈ (B.gf_votes.foldl
        (Protocol.on_goldfish_vote_checked S.E) stored).pool u.slot := by
      rw [hs, ModelProperties.mem_pool_iff, Protocol.update_finality_gf_votes] at hpost
      rw [ModelProperties.mem_pool_iff]
      exact hpost
    have hpre' : u ∉ stored.pool u.slot := by
      rw [ModelProperties.mem_pool_iff] at hpre ⊢
      exact hpre
    obtain ⟨j, hj, hlocal⟩ := fold_new_vote_origin S.E B.gf_votes stored u hpre' hfold
    exact ⟨j, ⟨hcall, hnew, hheld, hj⟩, hlocal⟩

omit [Fintype V] in
private theorem admit_rows_gf (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.gf_votes = st.core.gf_votes := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rows).core.gf_votes = st.core.gf_votes
    rw [ih, NamedAdmission.admit_row_core, Protocol.on_sg_vote_gf_votes]

/-- The full block handler `on_block_with` leaves the same Goldfish pool as `postCore`. -/
theorem block_with_gf_votes (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B).core.gf_votes =
      (postCore S before B).core.gf_votes := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact admit_rows_gf S.hc _ B.attestations
  · rfl

/-- `block_new_vote_origin` also holds for the full block handler `on_block_with`. -/
theorem block_with_new_vote_origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (B : NamedBlock V) (before : Protocol.NamedStore V)
    (hcall : blockCallAt S rho i v B before) (u : GoldfishVote V)
    (hpre : u ∉ before.core.pool u.slot)
    (hpost : u ∈ (Protocol.NamedAdmission.on_block_with
      .alsoCarried S.E S.hc S.cfg before B).core.pool u.slot) :
    ∃ j, carriedGoldfishAt S rho i v B j u before := by
  have hpost' : u ∈ (postCore S before B).core.pool u.slot := by
    rw [ModelProperties.mem_pool_iff] at hpost ⊢
    rw [← block_with_gf_votes S before B]
    exact hpost
  obtain ⟨j, hj, _⟩ := block_new_vote_origin S rho i v B before hcall u hpre hpost'
  exact ⟨j, hj⟩

#print axioms fold_new_vote_origin
#print axioms post_core_stored
#print axioms block_new_vote_origin
#print axioms block_with_gf_votes
#print axioms block_with_new_vote_origin
end DecoupledConsensusModel.Proofs.NamedReceiptCallsGF

/-! ## Origin of Goldfish votes at a tick -/
namespace DecoupledConsensusModel.Proofs.NamedReceiptCallsGF
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem named_vote_new_output (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (u : GoldfishVote V) (hpre : u ∉ st.core.pool u.slot)
    (hpost : u ∈ (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.pool u.slot) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).2 = some u := by
  simp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with] at hpost ⊢
  split_ifs at hpost ⊢
  · exact congrArg some (checked_new_vote_eq E st.core _ u hpre hpost)
  · exact False.elim (hpre hpost)

/-- A Goldfish vote new to the pool after a named tick comes from the tick's Goldfish emission or
    from the block call of the tick's own emitted block. -/
theorem tick_new_vote_origin (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (u : GoldfishVote V)
    (hpre : u ∉ st.core.pool u.slot)
    (hpost : u ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.pool u.slot) :
    NamedObject.gfVote u ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 ∨
      ∃ B : NamedBlock V,
        NamedObject.block B ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 ∧
        u ∉ (Protocol.NamedStore.setClock E st t).core.pool u.slot ∧
        u ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried E hc cfg
          (Protocol.NamedStore.setClock E st t) B).core.pool u.slot := by
  let s := E.slotOf t
  let st0 := Protocol.NamedStore.setClock E st t
  let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
  let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
  let st1 := if proposalDue then proposed.1 else st0
  let emitted1 : List (NamedObject V) := if proposalDue then
    match proposed.2 with
    | none => []
    | some B => [.block B]
  else []
  let voteDue := 0 < s ∧ t = Protocol.vote_time E s
  let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
  let st2 := if voteDue then voted.1 else st1
  let emitted2 : List (NamedObject V) :=
    if voteDue then voted.2.toList.map NamedObject.gfVote else []
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
    Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
  have hconfirm : st3.core.gf_votes = st2.core.gf_votes := by
    dsimp only [st3]
    split_ifs <;> rfl
  have hout := NamedTick.tick_computed_duties gc E hc cfg nd st record t
  change Protocol.NamedTick.tick gc E hc cfg nd st record t =
    (if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
      let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
      (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [.attest attested.2.2])
    else (st3, record, emitted1 ++ emitted2)) at hout
  have hfields : (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.gf_votes =
      st2.core.gf_votes := by
    rw [hout]
    split_ifs
    · rw [NamedDuties.attest_core, Protocol.on_sg_vote_gf_votes]
      exact hconfirm
    · exact hconfirm
  have hemit1 : ∀ o ∈ emitted1,
      o ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
    intro o ho
    rw [hout]
    split_ifs <;> simp [List.mem_append, ho]
  have hemit2 : ∀ o ∈ emitted2,
      o ∈ (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.2 := by
    intro o ho
    rw [hout]
    split_ifs <;> simp [List.mem_append, ho]
  have hafter2 : u ∈ st2.core.pool u.slot := by
    simpa only [Protocol.Store.pool, hfields] using hpost
  by_cases hin1 : u ∈ st1.core.pool u.slot
  · by_cases hd : proposalDue
    · cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried E hc nd st0 with
      | none =>
        have he := NamedDuties.propose_none gc E hc cfg nd st0 hp
        have h0 : u ∈ st0.core.pool u.slot := by
          simpa only [st1, proposed, if_pos hd, he] using hin1
        exact False.elim (hpre h0)
      | some B =>
        have he := NamedDuties.propose_some gc E hc cfg nd st0 B hp
        refine Or.inr ⟨B, hemit1 (.block B) ?_, hpre, ?_⟩
        · simp only [emitted1, proposed, if_pos hd, he]
          simp
        · simpa only [st1, proposed, if_pos hd, he] using hin1
    · have h0 : u ∈ st0.core.pool u.slot := by
        simpa only [st1, if_neg hd] using hin1
      exact False.elim (hpre h0)
  · by_cases hv : voteDue
    · have hvpost : u ∈ (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1).1.core.pool
          u.slot := by
        simpa only [st2, voted, if_pos hv] using hafter2
      have he := named_vote_new_output gc E hc nd st1 u hin1 hvpost
      apply Or.inl
      apply hemit2 (.gfVote u)
      simp [emitted2, voted, hv, he]
    · exact False.elim (hin1 (by simpa only [st2, if_neg hv] using hafter2))

#print axioms tick_new_vote_origin
end DecoupledConsensusModel.Proofs.NamedReceiptCallsGF

end
