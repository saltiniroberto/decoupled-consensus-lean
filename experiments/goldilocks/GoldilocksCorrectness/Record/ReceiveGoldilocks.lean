module
public import GoldilocksCorrectness.Record.ReceiveFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Routines.HeldAttestations
public import GoldilocksCorrectness.Proofs.Routines.TickFrame
public import GoldilocksCorrectness.Proofs.Routines.ACStore
public import GoldilocksCorrectness.Proofs.Routines.DREPost
import all Goldilocks.AC.State
import all Goldilocks.AC.Interface
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's receipt facts

`receiveFacts_goldilocks`: the spec's model satisfies `ReceiveFacts`. At `Model.goldilocks` a
delivery is the spec's `Goldilocks.Sts.receive`, which hands a block to `on_block`, a Goldfish vote
to `on_ac_message` and an attestation to `on_attestation`. Most fields are the landed theorems of
`GoldilocksCorrectness/Proofs/Routines/Wiring.lean`, `TickFrame.lean` and `ACStore.lean` (the
relations they conclude are, by definition, the conjunctions the fields write out); those that take
the model's node invariant pass its clause `ChainStatesComputed` to the landed theorem. The clock
and the validator are kept by a case split on the object. The votes of an accepted block
(`receive_block_votes`) are proved here, along the loop of `ac_on_block` over the block's votes,
from the landed `receive_gfVote_cases` and two facts on the admission of a vote: it only adds to
the votes of a slot, and a validator with two votes in a set has two in every larger set.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block Attestation GoldfishVote NamedObject
  ACState Time Slot)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The admission of a Goldfish vote keeps every vote of every slot's set of votes.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote admitted; `s`: a slot.

Read aloud: admitting a vote only adds to the votes held. -/
theorem pool_subset_on_goldfish_vote (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) (s : Slot) :
    A.pool s ⊆ (Goldilocks.on_goldfish_vote C P A t vote).pool s := by
  rcases GoldilocksCorrectness.Proofs.Routines.on_goldfish_vote_cases_new C P A t vote with
    he | ⟨-, he⟩
  · rw [he]
  · rw [he]
    intro x hx
    simp only [ACState.pool, GoldilocksCorrectness.Proofs.Routines.fun_getElem,
      List.mem_toFinset, Function.update_apply] at hx ⊢
    split
    · rename_i hs
      subst hs
      exact List.mem_append_left _ hx
    · exact hx

omit [Fintype V] in
/-- A validator with two distinct votes in a set of votes has two in every set holding it.

The variables:
- `S`, `S'`: the sets of votes; `v`: the validator.

Read aloud: an equivocation stays one as the votes grow. -/
theorem equivocates_of_subset {S S' : Finset (GoldfishVote V)} {v : V}
    (h : Goldilocks.equivocates S v = true) (hS : S ⊆ S') :
    Goldilocks.equivocates S' v = true := by
  simp only [Goldilocks.equivocates, Goldilocks.votes_by, decide_eq_true_eq] at h ⊢
  exact le_trans h (Finset.card_le_card (Finset.filter_subset_filter _ hS))

omit [Fintype V] in
/-- The admission, in list order, of the Goldfish votes of `l` at the time `t`, from the AC state
`A₀`: each vote of `l` whose slot is the slot of `t` or the one before, and whose validator is in
its slot's committee, is in the result's votes of its slot, or the result's votes of its slot hold
two distinct votes of its validator.

The variables:
- `C`, `P`: the parameters and the values; `t`: the admission time; `l`: the votes;
  `A₀`: the AC state the loop starts from.

Read aloud: admitting a list of votes admits each eligible one, unless its validator has
equivocated. -/
theorem forIn_on_goldfish_vote_admits (C : Config) (P : Provisional V) (t : Time)
    (l : List (GoldfishVote V)) (A₀ : ACState V) :
    ∀ vote ∈ l, C.slot t ≤ vote.slot + 1 → vote.slot ≤ C.slot t →
      vote.val_index ∈ P.committee vote.slot →
        vote ∈ (forIn (m := Id) l A₀ (fun vote' A =>
            Pure.pure (ForInStep.yield (Goldilocks.on_goldfish_vote C P A t vote')))).pool
            vote.slot ∨
          Goldilocks.equivocates ((forIn (m := Id) l A₀ (fun vote' A =>
            Pure.pure (ForInStep.yield (Goldilocks.on_goldfish_vote C P A t vote')))).pool
            vote.slot) vote.val_index = true := by
  induction l generalizing A₀ with
  | nil => intro vote hv; exact absurd hv (List.not_mem_nil)
  | cons a l ih =>
      intro vote hv hs1 hs2 hc
      rw [List.forIn_cons]
      rcases List.mem_cons.mp hv with rfl | hv
      · -- the vote is admitted first, and every later admission keeps it so
        refine GoldilocksCorrectness.Proofs.Routines.forIn_yield_inv l _
          (fun A vote' => Goldilocks.on_goldfish_vote C P A t vote')
          (fun A => vote ∈ A.pool vote.slot ∨
            Goldilocks.equivocates (A.pool vote.slot) vote.val_index = true) ?_ ?_
        · rcases GoldilocksCorrectness.Proofs.Routines.receive_gfVote_cases C P A₀ t vote hs1 hs2 hc
            with h | h
          · exact Or.inl h
          · exact Or.inr (equivocates_of_subset h (pool_subset_on_goldfish_vote C P A₀ t vote _))
        · intro A vote' _ hA
          rcases hA with h | h
          · exact Or.inl (pool_subset_on_goldfish_vote C P A t vote' _ h)
          · exact Or.inr (equivocates_of_subset h (pool_subset_on_goldfish_vote C P A t vote' _))
      · exact ih _ vote hv hs1 hs2 hc

/-- The spec's model satisfies the facts about the receipt.

Read aloud: a Goldilocks delivery adds to what the node holds only the delivered object and what it
carries, stamped with the clock, and changes no confirmation, lock, wake time, clock or
signature. -/
theorem receiveFacts_goldilocks : ReceiveFacts (Model.goldilocks (V := V)) where
  receive_keeps_confirmation C P X n o := by
    obtain ⟨h1, h2, h3, h4⟩ :=
      GoldilocksCorrectness.Proofs.Routines.receive_keeps_confirmation C P X n o
    refine ⟨h2, h3, h1, h4, GoldilocksCorrectness.Proofs.Routines.receive_awakeSince C P X n o, ?_⟩
    show (Goldilocks.Sts.receive C P X n o).t = n.t
    cases o with
    | block B =>
        show (Goldilocks.on_block C P X n B).t = _
        rw [GoldilocksCorrectness.Proofs.Routines.on_block_eq]
        split <;> rfl
    | gfVote vote => rfl
    | attest a => exact (GoldilocksCorrectness.Proofs.Routines.on_attestation_frame n a).2.2
  receive_validator C P X n o := by
    show (Goldilocks.Sts.receive C P X n o).v = n.v
    cases o with
    | block B =>
        show (Goldilocks.on_block C P X n B).v = _
        rw [GoldilocksCorrectness.Proofs.Routines.on_block_eq]
        split <;> rfl
    | gfVote vote => rfl
    | attest a =>
        show (Goldilocks.on_attestation n a).v = _
        simp only [Goldilocks.on_attestation, Id.run]
        split <;> rfl
  receive_Λ C P X n o := by
    have h := GoldilocksCorrectness.Proofs.Routines.receive_Λ C P X n o
    show (fun h => (Goldilocks.Sts.receive C P X n o).Λ.target h) = (fun h => n.Λ.target h) ∧
      (fun h => (Goldilocks.Sts.receive C P X n o).Λ.timeout h) = (fun h => n.Λ.timeout h) ∧
      (fun h => (Goldilocks.Sts.receive C P X n o).Λ.lock h) = (fun h => n.Λ.lock h) ∧
      (Goldilocks.Sts.receive C P X n o).Λ.sent = n.Λ.sent
    rw [h]
    exact ⟨rfl, rfl, rfl, rfl⟩
  receive_step C P X n o hk := GoldilocksCorrectness.Proofs.Routines.receive_step C P X n o hk
  receive_tree_mono C P X n o :=
    (GoldilocksCorrectness.Proofs.Routines.receive_reachFrom C P X Block.genesis n o).1
  receive_pool C P X n o := GoldilocksCorrectness.Proofs.Routines.receive_pool C P X n o
  receive_chainsInPool C P X n o h :=
    GoldilocksCorrectness.Proofs.Routines.receive_chainsInPool C P X n o h
  receive_finalizedFrom C P X n o h :=
    GoldilocksCorrectness.Proofs.Routines.receive_finalizedFrom C P X n o h.1.2.2.2.2.2.1
  receive_justifiedFrom C P X n o h :=
    GoldilocksCorrectness.Proofs.Routines.receive_justifiedFrom C P X n o h.1.2.2.2.2.2.1
  receive_cachesFrom C P X H OnChain n o h :=
    GoldilocksCorrectness.Proofs.Routines.receive_cachesFrom C P X H OnChain n o h.1.2.2.2.2.2.1
  receive_new C P X n o := GoldilocksCorrectness.Proofs.Routines.receive_new C P X n o
  receive_new_attestations C P X n o :=
    GoldilocksCorrectness.Proofs.Routines.receive_new_attestations C P X n o
  receive_new_slot C P X n o := GoldilocksCorrectness.Proofs.Routines.receive_new_slot C P X n o
  receive_gfVote_cases C P X n vote hs1 hs2 hc :=
    GoldilocksCorrectness.Proofs.Routines.receive_gfVote_cases C P n.A n.t vote hs1 hs2 hc
  receive_gfVote_admits C P X n vote := by
    show ((fun s => (Goldilocks.on_goldfish_vote C P n.A n.t vote).gf_votes s) =
          (fun s => n.A.gf_votes s) ∧
        (fun w => (Goldilocks.on_goldfish_vote C P n.A n.t vote).timestamp_vote w) =
          (fun w => n.A.timestamp_vote w)) ∨
      (vote ∉ n.A.gf_votes vote.slot ∧ vote.val_index ∈ P.committee vote.slot ∧
        (fun s => (Goldilocks.on_goldfish_vote C P n.A n.t vote).gf_votes s) =
          Function.update (fun s => n.A.gf_votes s) vote.slot (n.A.gf_votes vote.slot ++ [vote]) ∧
        (fun w => (Goldilocks.on_goldfish_vote C P n.A n.t vote).timestamp_vote w) =
          Function.update (fun w => n.A.timestamp_vote w) vote (some (n.t : Goldilocks.Stamp)))
    rcases GoldilocksCorrectness.Proofs.Routines.on_goldfish_vote_cases C P n.A n.t vote with
      he | ⟨hc, -⟩
    · rw [he]
      exact Or.inl ⟨rfl, rfl⟩
    rcases GoldilocksCorrectness.Proofs.Routines.on_goldfish_vote_cases_new C P n.A n.t vote with
      he | ⟨hnew, he⟩
    · rw [he]
      exact Or.inl ⟨rfl, rfl⟩
    · rw [he]
      exact Or.inr ⟨hnew, hc, rfl, rfl⟩
  receive_block_votes C P X n B hB hB' vote hv hs1 hs2 hc := by
    show vote ∈ (Goldilocks.on_block C P X n B).A.pool vote.slot ∨
      Goldilocks.equivocates ((Goldilocks.on_block C P X n B).A.pool vote.slot)
        vote.val_index = true
    change B ∈ (Goldilocks.on_block C P X n B).S.T at hB'
    rw [GoldilocksCorrectness.Proofs.Routines.on_block_eq] at hB' ⊢
    split
    · simp only [Goldilocks.ac_on_block, Id.run]
      exact forIn_on_goldfish_vote_admits C P n.t B.votes _ vote hv hs1 hs2 hc
    · rename_i hadm
      rw [if_neg hadm] at hB'
      exact absurd hB' hB
  receive_attestation_held C P X n a hw :=
    (GoldilocksCorrectness.Proofs.Routines.on_attestation_pool n a).2 hw
  mem_relayedObjects_iff o o' := by
    show o' ∈ Goldilocks.Sts.relayedObjects o ↔ _
    rw [GoldilocksCorrectness.Proofs.Routines.mem_relayedObjects_iff]
    cases o with
    | block B =>
        simp only [GoldilocksCorrectness.Statements.Routines.carries, NamedObject.block.injEq,
          exists_eq_left']
    | gfVote vote =>
        simp [GoldilocksCorrectness.Statements.Routines.carries]
    | attest a =>
        simp [GoldilocksCorrectness.Statements.Routines.carries]

end GoldilocksCorrectness.Record
