import Proofs.Claims.Spec2Claims.Claim13beRoute3_1
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_initial_stamp
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_attestations
import Proofs.Claims.Spec2Claims.Claim13bModel_poolRows
import Proofs.Claims.Spec2Claims.Claim13bModel_processedRows
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG2b
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_sg_pool
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_row_s4
import Proofs.Claims.Spec2Claims.Claim13bModel_on_goldfish_vote_checked_s4
import Proofs.Claims.Spec2Claims.Claim13bModel_update_finality_s4
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_goldfish_vote_with
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Vocabulary.ModelProperties.on_block_checked_using
import Proofs.Vocabulary.ModelProperties.on_block_using
import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
import Proofs.Vocabulary.ModelProperties.NamedStore_commitBlock
import Proofs.Vocabulary.ModelProperties.carried_attestations_admissible
import Proofs.Vocabulary.ModelProperties.NamedReceipt_process
import Proofs.Vocabulary.ModelProperties.propose_block_with
import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
import Proofs.Vocabulary.ModelProperties.update_confirmation_with
import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
import Proofs.Vocabulary.Protocol.Schedule.NamedTick

/-!
# Attestations refused for good, and what store operations preserve

The predicate `SgRefused` of an attestation the admission test refuses at a store and at every later
one, the predicate `IncludedAttestationsSettled`, and the structure `SgMono` of what every store
operation of a validator preserves, proved for each receipt, duty and tick.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Attestations refused for good -/

/-- The admission test refuses `b` at the core store `c` and at every later store: `b`'s round is
    more than `hc.η_SG` rounds before the store's round, or the confirmed block `b` names is already
    recorded for `b`'s signer and round, or two confirmed blocks are already recorded for them. -/
def SgRefused (hc : HealConfig) (c : Store V) (b : CombinedAttestation V) : Prop :=
  b.round < hc.round_of c.s - hc.η_SG ∨ b.confirmed ∈ round_votes c b ∨
    (round_votes c b).card = 2

omit [Fintype V] in
/-- `on_sg_vote` returns its store unchanged on an attestation `SgRefused` holds of. -/
theorem on_sg_vote_of_refused (hc : HealConfig) (c : Store V) (b : CombinedAttestation V)
    (h : SgRefused hc c b) : on_sg_vote hc c b = c := by
  apply on_sg_vote_of_rejected
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

omit [Fintype V] in
/-- Two attestations with the same round and signer have the same `round_votes`. -/
theorem round_votes_congr (c : Store V) {b b' : CombinedAttestation V}
    (hr : b'.round = b.round) (hv : b'.val_index = b.val_index) :
    round_votes c b' = round_votes c b := by
  ext o
  rw [Sts.mem_round_votes_iff, Sts.mem_round_votes_iff, hr, hv]

omit [Fintype V] in
/-- An attestation refused for good is still refused after the store runs `on_sg_vote` on any
    attestation. -/
theorem sgRefused_on_sg_vote (hc : HealConfig) (c : Store V) (b b' : CombinedAttestation V)
    (h : SgRefused hc c b) : SgRefused hc (on_sg_vote hc c b') b := by
  by_cases hacc : b'.round < hc.round_of c.s - hc.η_SG ∨ hc.round_of c.s < b'.round ∨
      b'.confirmed ∈ round_votes c b' ∨ (round_votes c b').card = 2
  · rw [on_sg_vote_of_rejected hc c b' hacc]
    exact h
  · have hsv := on_sg_vote_sg_votes_of_admitted hc c b' hacc
    push Not at hacc
    obtain ⟨-, -, hnot, hcard⟩ := hacc
    set c' : Store V := on_sg_vote hc c b' with hc'
    have hmem : ∀ z, z ∈ c'.sg_pool b.round ↔
        z ∈ (if b.round = b'.round then c.sg_votes b.round ++ [b'] else c.sg_votes b.round) := by
      intro z
      rw [Sts.mem_sg_pool_iff, hsv]
    have hsub : round_votes c b ⊆ round_votes c' b := by
      intro y hy
      rw [Sts.mem_round_votes_iff] at hy ⊢
      obtain ⟨z, hz, hzv, hzy⟩ := hy
      refine ⟨z, ?_, hzv, hzy⟩
      rw [hmem]
      rw [Sts.mem_sg_pool_iff] at hz
      split_ifs
      · exact List.mem_append_left _ hz
      · exact hz
    have heq : ¬ (b'.round = b.round ∧ b'.val_index = b.val_index) →
        round_votes c' b = round_votes c b := by
      intro hne
      ext y
      rw [Sts.mem_round_votes_iff, Sts.mem_round_votes_iff]
      constructor
      · rintro ⟨z, hz, hzv, hzy⟩
        refine ⟨z, ?_, hzv, hzy⟩
        rw [hmem] at hz
        rw [Sts.mem_sg_pool_iff]
        split_ifs at hz with hr
        · rcases List.mem_append.1 hz with hz | hz
          · exact hz
          · rw [List.mem_singleton] at hz
            subst hz
            exact absurd ⟨hr.symm, hzv⟩ hne
        · exact hz
      · rintro ⟨z, hz, hzv, hzy⟩
        refine ⟨z, ?_, hzv, hzy⟩
        rw [hmem]
        rw [Sts.mem_sg_pool_iff] at hz
        split_ifs
        · exact List.mem_append_left _ hz
        · exact hz
    have hs : c'.s = c.s := on_sg_vote_s' hc c b'
    rcases h with h | h | h
    · left; rw [hs]; exact h
    · right; left; exact hsub h
    · right; right
      by_cases hsame : b'.round = b.round ∧ b'.val_index = b.val_index
      · exfalso
        apply hcard
        rw [round_votes_congr c hsame.1 hsame.2]
        exact h
      · rw [heq hsame]; exact h


omit [Fintype V] in
/-- If two core stores hold the same `sg_votes` and the second's slot is at least the first's, an
    attestation refused for good at the first is refused for good at the second. -/
theorem sgRefused_of_frame (hc : HealConfig) {c c' : Store V} (b : CombinedAttestation V)
    (hsg : c'.sg_votes = c.sg_votes) (hs : c.s ≤ c'.s) (h : SgRefused hc c b) :
    SgRefused hc c' b := by
  have hrv : round_votes c' b = round_votes c b := by
    ext o
    simp only [Sts.mem_round_votes_iff, Sts.mem_sg_pool_iff, hsg]
  rcases h with h | h | h
  · left
    have hr : hc.round_of c.s ≤ hc.round_of c'.s := Sts.round_of_mono hc hs
    exact lt_of_lt_of_le h (Nat.sub_le_sub_right hr _)
  · right; left; rw [hrv]; exact h
  · right; right; rw [hrv]; exact h

/-- Every attestation `a` included in a body the store holds is among the store's rows of `a`'s
    round, or its erasure is refused for good at the store. -/
def IncludedAttestationsSettled (hc : HealConfig) (st : NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, ∀ a ∈ B.attestations, a ∈ st.sg_rows a.round ∨ SgRefused hc st.core a.erase

/-- The four properties every store operation of a validator preserves from `st` to `st'`. -/
structure SgMono (hc : HealConfig) (st st' : NamedStore V) : Prop where
  refused : ∀ b : CombinedAttestation V, SgRefused hc st.core b → SgRefused hc st'.core b
  rows : ∀ a : NamedAttestation V, a ∈ st.sg_rows a.round → a ∈ st'.sg_rows a.round
  excluded : ∀ a : NamedAttestation V, a ∉ st.sg_rows a.round →
    SgRefused hc st.core a.erase → a ∉ st'.sg_rows a.round
  settled : IncludedAttestationsSettled hc st → IncludedAttestationsSettled hc st'

omit [Fintype V] in
/-- `SgMono` is reflexive. -/
theorem SgMono.refl (hc : HealConfig) (st : NamedStore V) : SgMono hc st st :=
  ⟨fun _ h => h, fun _ h => h, fun _ h _ => h, fun h => h⟩

omit [Fintype V] in
/-- `SgMono` is transitive. -/
theorem SgMono.trans {hc : HealConfig} {st st' st'' : NamedStore V} (h1 : SgMono hc st st')
    (h2 : SgMono hc st' st'') : SgMono hc st st'' :=
  ⟨fun b h => h2.refused b (h1.refused b h), fun a h => h2.rows a (h1.rows a h),
    fun a h0 hr => h2.excluded a (h1.excluded a h0 hr) (h1.refused _ hr),
    fun h => h2.settled (h1.settled h)⟩

omit [Fintype V] in
/-- A store change that keeps the rows, the held bodies and the core `sg_votes`, and does not move
    the slot back, is `SgMono`. -/
theorem sgMono_of_frame (hc : HealConfig) {st st' : NamedStore V}
    (hrows : st'.sg_rows = st.sg_rows) (hbodies : st'.bodies = st.bodies)
    (hsg : st'.core.sg_votes = st.core.sg_votes) (hs : st.core.s ≤ st'.core.s) :
    SgMono hc st st' := by
  refine ⟨fun b h => sgRefused_of_frame hc b hsg hs h, fun a h => by rw [hrows]; exact h,
    fun a h _ => by rw [hrows]; exact h, fun h B hB a ha => ?_⟩
  rw [hbodies] at hB
  rcases h B hB a ha with h' | h'
  · left; rw [hrows]; exact h'
  · right; exact sgRefused_of_frame hc _ hsg hs h'

/-! ## The attestation receipt -/

omit [Fintype V] in
/-- The named attestation receipt `NamedAdmission.admit_row` is `SgMono`. -/
theorem sgMono_admit_row (hc : HealConfig) (st : NamedStore V) (row : NamedAttestation V) :
    SgMono hc st (NamedAdmission.admit_row hc st row) := by
  have hcore := admit_row_core' hc st row
  refine ⟨fun b h => by rw [hcore]; exact sgRefused_on_sg_vote hc _ b _ h,
    fun a h => sg_rows_admit_row_mono hc st row _ h, fun a h0 hr hmem => ?_,
    fun h B hB a ha => ?_⟩
  · rcases mem_sg_rows_admit_row hc st row a.round hmem with h' | h'
    · exact h0 h'
    · subst h'
      have hnoop := on_sg_vote_of_refused hc st.core a.erase hr
      by_cases hcond : a.erase ∉ st.core.sg_pool a.round ∧
          a.erase ∈ (on_sg_vote hc st.core a.erase).sg_pool a.round
      · rw [hnoop] at hcond
        exact hcond.1 hcond.2
      · rw [admit_row_sg_rows_of_not_new hc st a hcond] at hmem
        exact h0 hmem
  · rw [admit_row_bodies'] at hB
    rcases h B hB a ha with h' | h'
    · exact Or.inl (sg_rows_admit_row_mono hc st row _ h')
    · right; rw [hcore]; exact sgRefused_on_sg_vote hc _ _ _ h'

omit [Fintype V] in
/-- The receipt of a list of attestations is `SgMono`. -/
theorem sgMono_admit_rows (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : NamedStore V),
      SgMono hc st (NamedAdmission.admit_rows hc st rows)
  | [], st => by rw [admit_rows_nil]; exact SgMono.refl hc st
  | a :: rows, st => by
      rw [admit_rows_cons]
      exact (sgMono_admit_row hc st a).trans (sgMono_admit_rows hc rows _)

omit [Fintype V] in
/-- An attestation whose round is at most the store's round is, after the store's receipt of it,
    recorded or refused for good. -/
theorem admit_row_settles (hc : HealConfig) (st : NamedStore V) (a : NamedAttestation V)
    (hnf : a.round ≤ hc.round_of st.core.s) :
    a ∈ (NamedAdmission.admit_row hc st a).sg_rows a.round ∨
      SgRefused hc (NamedAdmission.admit_row hc st a).core a.erase := by
  by_cases hin : a ∈ st.sg_rows a.round
  · exact Or.inl (sg_rows_admit_row_mono hc st a _ hin)
  rw [admit_row_core']
  by_cases hacc : a.erase.round < hc.round_of st.core.s - hc.η_SG ∨
      hc.round_of st.core.s < a.erase.round ∨
      a.erase.confirmed ∈ round_votes st.core a.erase ∨ (round_votes st.core a.erase).card = 2
  · right
    have hnoop : on_sg_vote hc st.core a.erase = st.core :=
      on_sg_vote_of_rejected hc st.core a.erase hacc
    rw [hnoop]
    rcases hacc with h | h | h | h
    · exact Or.inl h
    · exact absurd h (Nat.not_lt.2 (by rw [namedAttestation_erase_round]; exact hnf))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · by_cases hpool : a.erase ∈ st.core.sg_pool a.erase.round
    · right
      exact sgRefused_on_sg_vote hc _ _ _
        (Or.inr (Or.inl (mem_round_votes_of_mem_sg_pool st.core a.erase hpool)))
    · left
      have hpost : a.erase ∈ (on_sg_vote hc st.core a.erase).sg_pool a.erase.round :=
        mem_on_sg_vote_sg_pool_of_not hc st.core a.erase hacc
      rw [namedAttestation_erase_round] at hpool hpost
      rw [admit_row_sg_rows_of_new hc st a ⟨hpool, hpost⟩]
      show a ∈ (if a.round = a.round then st.sg_rows a.round ++ [a] else st.sg_rows a.round)
      rw [if_pos rfl]
      exact List.mem_append_right _ (List.mem_singleton_self _)


/-! ## The block receipt -/

/-- A fold of `on_goldfish_vote_checked` over a list of votes keeps the store's slot. -/
theorem foldl_on_goldfish_vote_checked_s' (E : Env V) :
    ∀ (us : List (GoldfishVote V)) (c : Store V),
      (us.foldl (on_goldfish_vote_checked E) c).s = c.s
  | [], _ => rfl
  | u :: us, c => by
      rw [List.foldl_cons, foldl_on_goldfish_vote_checked_s' E us,
        on_goldfish_vote_checked_s']

/-- The checked block handler keeps the core `sg_votes` and the slot. -/
theorem on_block_checked_using_frame (hc : HealConfig) (E : Env V) (c : Store V) (B : Block V)
    (bs : ChainState V → ChainState V) :
    (on_block_checked_using (fun current => on_block_using E current B bs) hc c B).sg_votes
        = c.sg_votes ∧
      (on_block_checked_using (fun current => on_block_using E current B bs) hc c B).s
        = c.s := by
  by_cases hadm : carried_attestations_admissible hc B = true
  · rw [Proofs.ModelProperties.on_block_checked_using_of_admissible _ hc c hadm]
    by_cases hrej : (c.s < B.slot ∨ B ∈ c.T ∨ B.parent ∉ c.T) ∨ (!Block.preceq c.F B) = true ∨
        B.proposer? ≠ some (E.proposer B.slot) ∨ ¬ (B.parent.slot < B.slot)
    · rw [Proofs.ModelProperties.on_block_using_of_rejected E c B bs hrej]
      exact ⟨rfl, rfl⟩
    · have h1 : ¬ (c.s < B.slot ∨ B ∈ c.T ∨ B.parent ∉ c.T) := fun h => hrej (Or.inl h)
      have h2 : ¬ (!Block.preceq c.F B) = true := fun h => hrej (Or.inr (Or.inl h))
      have h3 : ¬ B.proposer? ≠ some (E.proposer B.slot) :=
        fun h => hrej (Or.inr (Or.inr (Or.inl h)))
      have h4 : ¬ ¬ (B.parent.slot < B.slot) := fun h => hrej (Or.inr (Or.inr (Or.inr h)))
      rw [Proofs.ModelProperties.on_block_using_of_accepted E c B bs h1 h2 h3 h4]
      exact ⟨by rw [update_finality_sg_votes, foldl_on_goldfish_vote_checked_sg_votes],
        by rw [update_finality_s', foldl_on_goldfish_vote_checked_s']⟩
  · rw [Proofs.ModelProperties.on_block_checked_using_of_not_admissible _ hc c hadm]
    exact ⟨rfl, rfl⟩

/-- If the checked block handler inserts `B` into the erased tree, every attestation `B` includes
    has a round at most the round of `B`'s slot, and `B`'s slot is at most the store's slot. -/
theorem on_block_checked_using_entry (hc : HealConfig) (E : Env V) (c : Store V) (B : Block V)
    (bs : ChainState V → ChainState V) (h0 : B ∉ c.T)
    (h1 : B ∈ (on_block_checked_using (fun current => on_block_using E current B bs) hc c B).T) :
    carried_attestations_admissible hc B = true ∧ B.slot ≤ c.s := by
  refine ⟨?_, ?_⟩
  · by_contra hadm
    rw [Proofs.ModelProperties.on_block_checked_using_of_not_admissible _ hc c hadm] at h1
    exact h0 h1
  · by_contra hs
    have hlt : c.s < B.slot := Nat.lt_of_not_le hs
    have hnoop : on_block_using E c B bs = c :=
      Proofs.ModelProperties.on_block_using_of_rejected E c B bs (Or.inl (Or.inl hlt))
    by_cases hadm : carried_attestations_admissible hc B = true
    · rw [Proofs.ModelProperties.on_block_checked_using_of_admissible _ hc c hadm, hnoop] at h1
      exact h0 h1
    · rw [Proofs.ModelProperties.on_block_checked_using_of_not_admissible _ hc c hadm] at h1
      exact h0 h1

/-- `NamedStore.process_block_core` keeps the rows, the core `sg_votes` and the slot. -/
theorem process_block_core_frame (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : NamedStore V) (B : NamedBlock V) :
    (NamedStore.process_block_core E hc cfg st B).sg_rows = st.sg_rows ∧
      (NamedStore.process_block_core E hc cfg st B).core.sg_votes = st.core.sg_votes ∧
      (NamedStore.process_block_core E hc cfg st B).core.s = st.core.s := by
  refine ⟨process_block_core_sg_rows E hc cfg st B, ?_⟩
  by_cases hp : B.parent ∈ st.bodies
  · rw [Proofs.ModelProperties.process_block_core_of_parent_mem E hc cfg hp, commitBlock_core]
    exact on_block_checked_using_frame hc E st.core B.erase _
  · rw [Proofs.ModelProperties.process_block_core_of_parent_not_mem E hc cfg hp]
    exact ⟨rfl, rfl⟩

/-- If `NamedStore.process_block_core` adds `B` to the held bodies, every attestation `B` includes
    has a round at most the store's round. -/
theorem process_block_core_entry (E : Env V) (hc : HealConfig) (cfg : HeightConfig)
    (st : NamedStore V) (B : NamedBlock V) (h0 : B ∉ st.bodies)
    (h1 : B ∈ (NamedStore.process_block_core E hc cfg st B).bodies) :
    ∀ a ∈ B.attestations, a.round ≤ hc.round_of st.core.s := by
  intro a ha
  by_cases hp : B.parent ∈ st.bodies
  · rw [Proofs.ModelProperties.process_block_core_of_parent_mem E hc cfg hp] at h1
    rcases Proofs.ModelProperties.mem_commitBlock_bodies h1 with ⟨hcond, -⟩ | h1'
    · obtain ⟨hadm, hsl⟩ := on_block_checked_using_entry hc E st.core B.erase _ hcond.1 hcond.2
      have hmem : a.erase ∈ B.erase.attestations := by
        rw [Proofs.NamedWire.erase_attestations]
        exact List.mem_map_of_mem ha
      have hr : a.erase.round ≤ hc.round_of B.erase.slot :=
        (Proofs.ModelProperties.carried_attestations_admissible_eq_true_iff hc B.erase).1 hadm _
          hmem
      have hmono : hc.round_of B.erase.slot ≤ hc.round_of st.core.s :=
        Sts.round_of_mono hc hsl
      rw [namedAttestation_erase_round] at hr
      exact le_trans hr hmono
    · exact absurd h1' h0
  · rw [Proofs.ModelProperties.process_block_core_of_parent_not_mem E hc cfg hp] at h1
    exact absurd h1 h0

omit [Fintype V] in
/-- If every attestation of `rows` has a round at most the store's round, then after the receipts of
    `rows` each of them is recorded or refused for good. -/
theorem admit_rows_settles (hc : HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : NamedStore V),
      (∀ a ∈ rows, a.round ≤ hc.round_of st.core.s) →
      ∀ a ∈ rows, a ∈ (NamedAdmission.admit_rows hc st rows).sg_rows a.round ∨
        SgRefused hc (NamedAdmission.admit_rows hc st rows).core a.erase
  | [], _, _, _, ha => absurd ha List.not_mem_nil
  | b :: rows, st, hnf, a, ha => by
      rw [admit_rows_cons]
      have hs : (NamedAdmission.admit_row hc st b).core.s = st.core.s := by
        rw [admit_row_core']; exact on_sg_vote_s' hc st.core b.erase
      rcases List.mem_cons.1 ha with hab | ha'
      · subst hab
        have hm := sgMono_admit_rows hc rows (NamedAdmission.admit_row hc st a)
        rcases admit_row_settles hc st a (hnf a List.mem_cons_self) with h | h
        · exact Or.inl (hm.rows a h)
        · exact Or.inr (hm.refused _ h)
      · exact admit_rows_settles hc rows _
          (fun y hy => by rw [hs]; exact hnf y (List.mem_cons_of_mem _ hy)) a ha'

/-- The named block receipt `NamedAdmission.on_block_with` is `SgMono`. -/
theorem sgMono_on_block_with (adm : CarriedAdmission) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : NamedStore V) (B : NamedBlock V) :
    SgMono hc st (NamedAdmission.on_block_with adm E hc cfg st B) := by
  obtain ⟨hrows, hsg, hs⟩ := process_block_core_frame E hc cfg st B
  set st1 := NamedStore.process_block_core E hc cfg st B with hst1
  have href : ∀ b, SgRefused hc st.core b → SgRefused hc st1.core b :=
    fun b h => sgRefused_of_frame hc b hsg (le_of_eq hs.symm) h
  have hbod : ∀ C ∈ st1.bodies, C ∈ st.bodies ∨ C = B :=
    fun C hC => process_block_core_bodies_upper E hc cfg st B C hC
  have hset1 : IncludedAttestationsSettled hc st → ∀ C ∈ st1.bodies, C ∈ st.bodies →
      ∀ a ∈ C.attestations, a ∈ st1.sg_rows a.round ∨ SgRefused hc st1.core a.erase := by
    intro h C _ hC a ha
    rcases h C hC a ha with h' | h'
    · left; rw [hrows]; exact h'
    · right; exact href _ h'
  have hm1 : SgMono hc st1 st1 := SgMono.refl hc st1
  by_cases hcond : B ∉ st.bodies ∧ B ∈ st1.bodies
  · rw [on_block_with_of_new adm E hc cfg st B hcond.1 hcond.2, ← hst1]
    have hm2 := sgMono_admit_rows hc B.attestations st1
    have hnf : ∀ a ∈ B.attestations, a.round ≤ hc.round_of st1.core.s := by
      rw [hs]; exact process_block_core_entry E hc cfg st B hcond.1 hcond.2
    refine ⟨fun b h => hm2.refused b (href b h), fun a h => hm2.rows a (by rw [hrows]; exact h),
      fun a h0 hr => hm2.excluded a (by rw [hrows]; exact h0) (href _ hr), fun h C hC a ha => ?_⟩
    rw [admit_rows_bodies] at hC
    rcases hbod C hC with hC' | hC'
    · rcases hset1 h C hC hC' a ha with h' | h'
      · exact Or.inl (hm2.rows a h')
      · exact Or.inr (hm2.refused _ h')
    · subst hC'
      exact admit_rows_settles hc C.attestations st1 hnf a ha
  · rw [on_block_with_of_not_new adm E hc cfg st B hcond, ← hst1]
    refine ⟨href, fun a h => by rw [hrows]; exact h, fun a h0 _ => by rw [hrows]; exact h0,
      fun h C hC a ha => ?_⟩
    rcases hbod C hC with hC' | hC'
    · exact hset1 h C hC hC' a ha
    · subst hC'
      by_cases hin : C ∈ st.bodies
      · exact hset1 h C hC hin a ha
      · exact absurd ⟨hin, hC⟩ hcond

/-- A validator's receipt `NamedReceipt.process` of any delivered object is `SgMono`. -/
theorem sgMono_process (S : Setup V) (st : NamedStore V) (o : NamedObject V) :
    SgMono S.hc st (NamedReceipt.process S st o) := by
  cases o with
  | block B =>
      rw [Proofs.ModelProperties.process_block]
      exact sgMono_on_block_with .alsoCarried S.E S.hc S.cfg st B
  | gfVote u =>
      rw [Proofs.ModelProperties.process_gfVote]
      exact sgMono_of_frame S.hc rfl rfl (on_goldfish_vote_checked_sg_votes S.E st.core u)
        (le_of_eq (on_goldfish_vote_checked_s' S.E st.core u).symm)
  | attest a =>
      rw [Proofs.ModelProperties.process_attest]
      exact sgMono_admit_row S.hc st a


/-! ## The tick -/

/-- The named proposal duty is `SgMono`. -/
theorem sgMono_propose (gc : GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Node V) (st : NamedStore V) :
    SgMono hc st (NamedDuties.propose_block_with gc E hc cfg nd st).1 := by
  cases hp : NamedActions.proposal_with gc .poolAndCarried E hc nd st with
  | none =>
    rw [Proofs.ModelProperties.propose_block_with_fst_of_none gc E hc cfg nd st hp]
    exact SgMono.refl hc st
  | some B =>
    rw [Proofs.ModelProperties.propose_block_with_fst_of_some gc E hc cfg nd st hp]
    exact sgMono_on_block_with .alsoCarried E hc cfg st B

/-- The named Goldfish vote duty is `SgMono`. -/
theorem sgMono_vote (gc : GradeContract V) (E : Env V) (hc : HealConfig) (nd : Node V)
    (st : NamedStore V) :
    SgMono hc st (NamedDuties.goldfish_vote_with gc E hc nd st).1 := by
  have hframe : (Protocol.goldfish_vote_with gc E hc nd st.core).1.sg_votes = st.core.sg_votes ∧
      (Protocol.goldfish_vote_with gc E hc nd st.core).1.s = st.core.s := by
    rcases goldfish_vote_with_fst_cases gc E hc nd st.core with h | ⟨u, h⟩
    · rw [h]
      exact ⟨rfl, rfl⟩
    · rw [h]
      exact ⟨on_goldfish_vote_checked_sg_votes E st.core _, on_goldfish_vote_checked_s' E st.core _⟩
  have hcore := namedDuties_goldfish_vote_with_fst_core gc E hc nd st
  exact sgMono_of_frame hc (namedDuties_goldfish_vote_with_fst_sg_rows gc E hc nd st)
    (namedDuties_goldfish_vote_with_fst_bodies gc E hc nd st) (by rw [hcore]; exact hframe.1)
    (le_of_eq (by rw [hcore]; exact hframe.2.symm))

/-- The named confirmation duty is `SgMono`. -/
theorem sgMono_confirmation (gc : GradeContract V) (E : Env V) (hc : HealConfig)
    (st : NamedStore V) (s : Slot) :
    SgMono hc st (NamedDuties.update_confirmation_with gc E hc st s) :=
  sgMono_of_frame hc (namedDuties_update_confirmation_with_sg_rows gc E hc st s)
    (namedDuties_update_confirmation_with_bodies gc E hc st s)
    (by rw [Proofs.ModelProperties.named_update_confirmation_with_core,
      update_confirmation_with_sg_votes_eq])
    (le_of_eq (by rw [Proofs.ModelProperties.named_update_confirmation_with_core,
      Proofs.ModelProperties.update_confirmation_with_s]))

/-- The named attestation duty is `SgMono`. -/
theorem sgMono_attest (gc : GradeContract V) (E : Env V) (hc : HealConfig) (nd : Node V)
    (st : NamedStore V) (record : NamedRecord) :
    SgMono hc st (NamedDuties.attest_with gc E hc nd st record).1 := by
  rw [namedDuties_attest_with_fst]
  exact sgMono_admit_row hc st _

/-- The named tick at instant `t` is `SgMono` when the slot of `t` is at least the store's slot. -/
theorem sgMono_named_tick (gc : GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Node V) (st : NamedStore V) (record : NamedRecord) (t : Int)
    (hs : st.core.s ≤ E.slotOf t) :
    SgMono hc st (NamedTick.tick gc E hc cfg nd st record t).1 := by
  have hclock : SgMono hc st (Protocol.NamedStore.setClock E st t) :=
    sgMono_of_frame hc (setClock_sg_rows E st t) (Proofs.ModelProperties.setClock_bodies E st t)
      (setClock_core_sg_votes E st t) (by rw [Sts.setClock_core_s]; exact hs)
  have hprop : ∀ st' : NamedStore V, SgMono hc st st' →
      SgMono hc st (NamedDuties.propose_block_with gc E hc cfg nd st').1 :=
    fun st' h => h.trans (sgMono_propose gc E hc cfg nd st')
  have hvote : ∀ st' : NamedStore V, SgMono hc st st' →
      SgMono hc st (NamedDuties.goldfish_vote_with gc E hc nd st').1 :=
    fun st' h => h.trans (sgMono_vote gc E hc nd st')
  have hconf : ∀ (st' : NamedStore V) (s : Slot), SgMono hc st st' →
      SgMono hc st (NamedDuties.update_confirmation_with gc E hc st' s) :=
    fun st' s h => h.trans (sgMono_confirmation gc E hc st' s)
  have hatt : ∀ (st' : NamedStore V) (r : NamedRecord), SgMono hc st st' →
      SgMono hc st (NamedDuties.attest_with gc E hc nd st' r).1 :=
    fun st' r h => h.trans (sgMono_attest gc E hc nd st' r)
  rw [Proofs.NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;>
    repeat' first
      | exact hclock
      | apply hatt
      | apply hconf
      | apply hvote
      | apply hprop

/-- `NamedNode.tick` at instant `t` is `SgMono` when the slot of `t` is at least the store's slot. -/
theorem sgMono_node_tick (S : Setup V) (v : V) (n : NamedNodeState V) (t : Int)
    (hs : n.st.core.s ≤ S.E.slotOf t) :
    SgMono S.hc n.st (NamedNode.tick S v n t).1.st := by
  rw [namedNode_tick_st]
  exact sgMono_named_tick _ S.E S.hc S.cfg (S.node v) n.st n.record t hs


end DecoupledConsensusModel.Sts
