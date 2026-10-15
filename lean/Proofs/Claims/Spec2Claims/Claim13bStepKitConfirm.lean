module
public import Proofs.Claims.Spec2Claims.Claim13bStepKitRelay
public import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_equivocates
public import Proofs.Claims.Spec2Claims.Claim13bModel_slotStart
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_poolStamps
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2
public import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
public import Proofs.Claims.Spec2Claims.Claim13bModel_stampedBefore
public import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
public import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_RootInjectiveBelow
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
public import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote_checked_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_rows_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with_mk_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_vote_with
public import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with_mk_s3
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
public import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau_mk
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
public import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
public import Proofs.Vocabulary.ModelProperties.on_goldfish_vote_checked
public import Proofs.Vocabulary.ModelProperties.on_block_using
public import Proofs.Vocabulary.ModelProperties.on_block_checked_using
public import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
public import Proofs.Vocabulary.ModelProperties.propose_block_with
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.NamedNode_process
public import Proofs.Vocabulary.ModelProperties.NamedReceipt_process

@[expose] public section

/-!
# Goldfish vote stamps at insertion, and `live_confirmed` across the attestation duty

The predicate `InsertsAt` of a store write at one clock reading, under which every Goldfish vote
that enters is stamped with that clock, proved for each handler and duty; and facts on the
`live_confirmed` field across the attestation duty.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## A vote's stamp at insertion is the store's clock -/

/-- What a store write from `st` to `st'` at clock reading `c` leaves behind. -/
structure InsertsData (E : Env V) (c : Int) (st st' : Protocol.Store V) : Prop where
  /-- Every vote and every stamp of `st` is still held in `st'`. -/
  carry : Protocol.PoolCarry st st'
  /-- `st'` satisfies `Protocol.PoolStamps`. -/
  stamps : Protocol.PoolStamps st'
  /-- The clock of `st'` reads `c`. -/
  clock : st'.t = c
  /-- The slot field is unchanged. -/
  slot : st'.s = st.s
  /-- A vote that entered is stamped with `c`, has a slot at most `st.s`, and is signed by a member
      of its slot's committee. -/
  new : ∀ u : GoldfishVote V, u ∉ st.gf_votes u.slot → u ∈ st'.gf_votes u.slot →
    st'.timestamp_vote u = some (c : Stamp) ∧ u.slot ≤ st.s ∧
      u.val_index ∈ E.committee u.slot

/-- The write from `st` to `st'` leaves `InsertsData E c st st'` whenever `st` satisfies
    `Protocol.PoolStamps` and its clock reads `c`. -/
def InsertsAt (E : Env V) (c : Int) (st st' : Protocol.Store V) : Prop :=
  Protocol.PoolStamps st → st.t = c → InsertsData E c st st'

namespace InsertsAt

variable {E : Env V} {c : Int} {st st' st'' : Protocol.Store V}

/-- `InsertsAt` is reflexive. -/
theorem refl' (E : Env V) (c : Int) (st : Protocol.Store V) : InsertsAt E c st st := by
  intro hps hc
  exact ⟨⟨fun _ _ hu => hu, fun _ _ h => h⟩, hps, hc, rfl, fun _ h0 h1 => absurd h1 h0⟩

/-- `InsertsAt` is transitive at one clock reading. -/
theorem trans' (h₁ : InsertsAt E c st st') (h₂ : InsertsAt E c st' st'') :
    InsertsAt E c st st'' := by
  intro hps hc
  obtain ⟨c₁, s₁, k₁, l₁, n₁⟩ := h₁ hps hc
  obtain ⟨c₂, s₂, k₂, l₂, n₂⟩ := h₂ s₁ k₁
  refine ⟨⟨fun k u hu => c₂.mem k u (c₁.mem k u hu),
    fun u τ hτ => c₂.stamp u τ (c₁.stamp u τ hτ)⟩, s₂, k₂, l₂.trans l₁, ?_⟩
  intro u h0 h1
  by_cases hm : u ∈ st'.gf_votes u.slot
  · obtain ⟨hst, hsl, hcm⟩ := n₁ u h0 hm
    exact ⟨c₂.stamp u _ hst, hsl, hcm⟩
  · obtain ⟨hst, hsl, hcm⟩ := n₂ u hm h1
    exact ⟨hst, l₁ ▸ hsl, hcm⟩

/-- A write that changes none of `gf_votes`, `timestamp_vote`, `t` and `s` satisfies `InsertsAt`. -/
theorem of_eq (hg : st'.gf_votes = st.gf_votes)
    (hv : st'.timestamp_vote = st.timestamp_vote) (ht : st'.t = st.t) (hs : st'.s = st.s) :
    InsertsAt E c st st' := by
  intro hps hc
  obtain ⟨hcarry, hstamps⟩ := Protocol.PoolStep.of_eq hg hv ht hps
  refine ⟨hcarry, hstamps, ht.trans hc, hs, ?_⟩
  intro u h0 h1
  rw [hg] at h1
  exact absurd h1 h0

/-- A `Protocol.PoolStep` that leaves `gf_votes`, `t` and `s` unchanged satisfies `InsertsAt`. -/
theorem of_poolStep (hstep : Protocol.PoolStep st st') (hg : st'.gf_votes = st.gf_votes)
    (ht : st'.t = st.t) (hs : st'.s = st.s) : InsertsAt E c st st' := by
  intro hps hc
  obtain ⟨hcarry, hstamps⟩ := hstep hps
  refine ⟨hcarry, hstamps, ht.trans hc, hs, ?_⟩
  intro u h0 h1
  rw [hg] at h1
  exact absurd h1 h0

end InsertsAt

/-- The checked Goldfish receipt of `u` satisfies `InsertsAt`: the only vote it can add is `u`. -/
theorem insertsAt_on_goldfish_vote_checked (E : Env V) (c : Int) (st : Protocol.Store V)
    (u : GoldfishVote V) : InsertsAt E c st (Protocol.on_goldfish_vote_checked E st u) := by
  intro hps hc
  obtain ⟨hcarry, hstamps⟩ := Protocol.poolStep_on_goldfish_vote_checked E st u hps
  refine ⟨hcarry, hstamps, (on_goldfish_vote_checked_time E st u).trans hc,
    on_goldfish_vote_checked_slot E st u, ?_⟩
  intro z h0 h1
  by_cases hk : u.val_index ∈ E.committee u.slot
  · have hch : Protocol.on_goldfish_vote_checked E st u = Protocol.on_goldfish_vote st u :=
      Proofs.ModelProperties.on_goldfish_vote_checked_of_mem_committee E st u hk
    rw [hch] at h1 ⊢
    by_cases hg1 : u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot
    · rw [on_goldfish_vote_of_rejected st u hg1] at h1
      exact absurd h1 h0
    by_cases hg2 : Protocol.equivocates (st.pool u.slot) u.val_index = true
    · rw [on_goldfish_vote_of_equivocates st u hg1 hg2] at h1
      exact absurd h1 h0
    obtain ⟨hgf, hts, -⟩ := Protocol.on_goldfish_vote_insert st u hg1 hg2
    have hzu : z = u := by
      simp only [hgf] at h1
      split_ifs at h1 with hkk
      · rcases List.mem_append.mp h1 with h | h
        · exact absurd h h0
        · exact List.mem_singleton.mp h
      · exact absurd h1 h0
    subst hzu
    have hsle : z.slot ≤ st.s := Nat.le_of_not_lt (fun h => hg1 (Or.inr (Or.inl h)))
    refine ⟨?_, hsle, hk⟩
    rw [hts]
    simp [hc]
  · rw [on_goldfish_vote_checked_of_not_mem_committee E st u hk] at h1
    exact absurd h1 h0

/-- The fold of `Protocol.on_goldfish_vote_checked` over a list of votes satisfies `InsertsAt`. -/
theorem insertsAt_foldl_on_goldfish_vote_checked (E : Env V) (c : Int)
    (l : List (GoldfishVote V)) :
    ∀ st : Protocol.Store V,
      InsertsAt E c st (l.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction l with
  | nil => intro st; exact InsertsAt.refl' E c st
  | cons u l ih =>
      intro st
      rw [List.foldl_cons]
      exact InsertsAt.trans' (insertsAt_on_goldfish_vote_checked E c st u) (ih _)

/-- `Protocol.update_finality` satisfies `InsertsAt`. -/
theorem insertsAt_update_finality (E : Env V) (c : Int) (st : Protocol.Store V)
    (σ : Protocol.ChainState V) : InsertsAt E c st (Protocol.update_finality st σ) :=
  InsertsAt.of_poolStep (Protocol.poolStep_update_finality st σ)
    (Protocol.update_finality_gf_votes st σ) (update_finality_time st σ)
    (update_finality_slot st σ)

/-- `Protocol.on_sg_vote` satisfies `InsertsAt`. -/
theorem insertsAt_on_sg_vote (E : Env V) (c : Int) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (a : CombinedAttestation V) :
    InsertsAt E c st (Protocol.on_sg_vote hc st a) :=
  InsertsAt.of_poolStep (Protocol.poolStep_on_sg_vote hc st a)
    (Protocol.on_sg_vote_gf_votes hc st a) (on_sg_vote_time hc st a)
    (on_sg_vote_slot hc st a)

/-- `Protocol.on_block_using` satisfies `InsertsAt`, whatever chain state `buildState` builds. -/
theorem insertsAt_on_block_using (E : Env V) (c : Int) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    InsertsAt E c st (Protocol.on_block_using E st B buildState) := by
  by_cases h1 : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B buildState (Or.inl h1)]
    exact InsertsAt.refl' E c st
  by_cases h2 : (!Block.preceq st.F B) = true
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B buildState
      (Or.inr (Or.inl h2))]
    exact InsertsAt.refl' E c st
  by_cases h3 : B.proposer? ≠ some (E.proposer B.slot)
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B buildState
      (Or.inr (Or.inr (Or.inl h3)))]
    exact InsertsAt.refl' E c st
  by_cases h4 : ¬ (B.parent.slot < B.slot)
  · rw [Proofs.ModelProperties.on_block_using_of_rejected E st B buildState
      (Or.inr (Or.inr (Or.inr h4)))]
    exact InsertsAt.refl' E c st
  rw [Proofs.ModelProperties.on_block_using_of_accepted E st B buildState h1 h2 h3 h4]
  refine InsertsAt.trans' ?_ (insertsAt_update_finality E c _ _)
  refine InsertsAt.trans' ?_ (insertsAt_foldl_on_goldfish_vote_checked E c B.gf_votes _)
  exact InsertsAt.of_eq rfl rfl rfl rfl

/-- `Protocol.on_block_checked_using` satisfies `InsertsAt` whenever the body `handle` it wraps
    does. -/
theorem insertsAt_on_block_checked_using (E : Env V) (c : Int)
    (handle : Protocol.Store V → Protocol.Store V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (B : Block V) (hh : InsertsAt E c st (handle st)) :
    InsertsAt E c st (Protocol.on_block_checked_using handle hc st B) := by
  by_cases hadm : Protocol.carried_attestations_admissible hc B = true
  · rw [Proofs.ModelProperties.on_block_checked_using_of_admissible handle hc st hadm]
    exact hh
  · rw [Proofs.ModelProperties.on_block_checked_using_of_not_admissible handle hc st hadm]
    exact InsertsAt.refl' E c st

/-- `Protocol.NamedAdmission.admit_row` satisfies `InsertsAt` on the core store. -/
theorem insertsAt_admit_row (E : Env V) (c : Int) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (row : NamedAttestation V) :
    InsertsAt E c st.core (Protocol.NamedAdmission.admit_row hc st row).core := by
  rw [admit_row_core]
  exact insertsAt_on_sg_vote E c hc st.core row.erase

/-- `Protocol.NamedAdmission.admit_rows` satisfies `InsertsAt` on the core store. -/
theorem insertsAt_admit_rows (E : Env V) (c : Int) (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      InsertsAt E c st.core (Protocol.NamedAdmission.admit_rows hc st rows).core
  | [], st => by
      rw [admit_rows_nil']
      exact InsertsAt.refl' E c st.core
  | row :: rows, st => by
      rw [admit_rows_cons']
      exact InsertsAt.trans' (insertsAt_admit_row E c hc st row)
        (insertsAt_admit_rows E c hc rows (Protocol.NamedAdmission.admit_row hc st row))

/-- `Protocol.NamedStore.process_block_core` satisfies `InsertsAt` on the core store. -/
theorem insertsAt_process_block_core (E : Env V) (c : Int) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    InsertsAt E c st.core (Protocol.NamedStore.process_block_core E hc cfg st B).core := by
  by_cases hp : B.parent ∈ st.bodies
  · rw [Proofs.ModelProperties.process_block_core_of_parent_mem E hc cfg hp, commitBlock_core]
    exact insertsAt_on_block_checked_using E c _ hc st.core B.erase
      (insertsAt_on_block_using E c st.core B.erase _)
  · rw [Proofs.ModelProperties.process_block_core_of_parent_not_mem E hc cfg hp]
    exact InsertsAt.refl' E c st.core

/-- The named block admission satisfies `InsertsAt` on the core store. -/
theorem insertsAt_on_block_with (E : Env V) (c : Int) (adm : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    InsertsAt E c st.core (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core := by
  have hcore := insertsAt_process_block_core E c hc cfg st B
  cases adm with
  | alsoCarried =>
      by_cases hnew : B ∉ st.bodies ∧
          B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies
      · rw [on_block_with_of_new' .alsoCarried E hc cfg st B hnew]
        exact InsertsAt.trans' hcore
          (insertsAt_admit_rows E c hc B.attestations
            (Protocol.NamedStore.process_block_core E hc cfg st B))
      · rw [on_block_with_of_not_new' .alsoCarried E hc cfg st B hnew]
        exact hcore

/-- The Goldfish vote duty satisfies `InsertsAt`, at any grade contract. -/
theorem insertsAt_goldfish_vote_with (E : Env V) (c : Int)
    (contract : Protocol.GradeContract V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.Store V) :
    InsertsAt E c st (Protocol.goldfish_vote_with contract E hc nd st).1 := by
  rcases goldfish_vote_with_fst_cases' contract E hc nd st with h | ⟨u, h⟩
  · rw [h]
    exact InsertsAt.refl' E c st
  · rw [h]
    exact insertsAt_on_goldfish_vote_checked E c _ _

/-- The named proposal duty satisfies `InsertsAt` on the core store. -/
theorem insertsAt_named_propose (E : Env V) (c : Int) (contract : Protocol.GradeContract V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    InsertsAt E c st.core
      (Protocol.NamedDuties.propose_block_with contract E hc cfg nd st).1.core := by
  cases hprop : Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none =>
      rw [Proofs.ModelProperties.propose_block_with_fst_of_none contract E hc cfg nd st hprop]
      exact InsertsAt.refl' E c st.core
  | some B =>
      rw [Proofs.ModelProperties.propose_block_with_fst_of_some contract E hc cfg nd st hprop]
      exact insertsAt_on_block_with E c .alsoCarried hc cfg st _

/-- The named Goldfish vote duty satisfies `InsertsAt` on the core store. -/
theorem insertsAt_named_vote (E : Env V) (c : Int) (contract : Protocol.GradeContract V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    InsertsAt E c st.core
      (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core := by
  rw [namedDuties_goldfish_vote_with_fst_core]
  exact insertsAt_goldfish_vote_with E c contract hc nd st.core

/-- The named confirmation duty satisfies `InsertsAt` on the core store. -/
theorem insertsAt_named_confirmation (E : Env V) (c : Int)
    (contract : Protocol.GradeContract V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) :
    InsertsAt E c st.core
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).core := by
  rw [Proofs.ModelProperties.named_update_confirmation_with_core]
  obtain ⟨hg, hv, ht⟩ := update_confirmation_with_vote_fields contract E hc st.core s
  exact InsertsAt.of_eq hg hv ht (Proofs.ModelProperties.update_confirmation_with_s _ _ _ _ _)

/-- The named attestation duty satisfies `InsertsAt` on the core store. -/
theorem insertsAt_named_attest (E : Env V) (c : Int) (contract : Protocol.GradeContract V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    InsertsAt E c st.core
      (Protocol.NamedDuties.attest_with contract E hc nd st record).1.core := by
  obtain ⟨row, hrow⟩ := namedDuties_attest_with_fst_exists_row contract E hc nd st record
  rw [hrow]
  exact insertsAt_admit_row E c hc st row

/-- A validator awake at every instant of `[t_0, t_1]` is awake at every instant of `[t_2, t_3]`
    whenever `t_0 ≤ t_2` and `t_3 ≤ t_1`. -/
theorem awakeThroughout_mono (Sched : Schedule V) {t_0 t_1 t_2 t_3 : Int} {w : V}
    (hawT : w ∈ Sched.awakeThroughout t_0 t_1) (h02 : t_0 ≤ t_2) (h31 : t_3 ≤ t_1) :
    w ∈ Sched.awakeThroughout t_2 t_3 := by
  have hsub : Sched.awakeThroughout t_0 t_1 ≤ Sched.awakeThroughout t_2 t_3 :=
    Finset.inf_mono (Finset.Icc_subset_Icc h02 h31)
  exact Finset.mem_of_subset hsub hawT

section

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

end

/-! ## `live_confirmed` across the attestation duty -/

omit [Fintype V] in
/-- Named row admission leaves `live_confirmed` of the core store as `Protocol.on_sg_vote` leaves
    it. -/
theorem admit_row_live_confirmed (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st row).core.live_confirmed
      = st.core.live_confirmed := by
  rw [admit_row_core]
  exact on_sg_vote_live_confirmed hc st.core row.erase

/-- The attestation duty leaves `live_confirmed` unchanged. -/
theorem attest_with_live_confirmed (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.live_confirmed
      = st.core.live_confirmed := by
  obtain ⟨row, hrow⟩ := namedDuties_attest_with_fst_exists_row gc E hc nd st record
  rw [hrow]
  exact admit_row_live_confirmed hc st row

end DecoupledConsensusModel.Sts
