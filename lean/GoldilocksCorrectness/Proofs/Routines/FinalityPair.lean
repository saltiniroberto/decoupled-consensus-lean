module
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.Certificates
public import GoldilocksCorrectness.Proofs.Routines.Walk
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# Lemmas 92 and 93: the finality pair carried and counted

The proofs of `lem92_attestation_carries_finality_pair` and `lem93_block_finalizes_pending`,
stated in `GoldilocksCorrectness/Statements/Routines/FinalityPairStatements.lean`.

The route of Lemma 92: `finality_pair` returns `(h_j, J)` when its four tests pass
(`finality_pair_eq_some`); `height_pair` gives a vote at `h_c`; `create_attestation` keeps the pair,
its height `h_j` being less than `h_c`.

The route of Lemma 93: counting an attestation keeps every validator of a finality participation
and adds the attestation's validator when its finality pair names a pending justification
(`process_attestation_finality_mono`, `process_attestation_finality_add`), so the fold over the
block's attestations leaves the quorum counted for the pending justification
(`foldl_finality_participation`); the loop over the pending justifications of
`process_height_events`, on a list in strictly increasing order of heights, leaves a finalization
height at least that of every pending justification whose finality participation is a quorum
(`pending_loop`, `process_height_events_h_F_ge`); the pending justifications of every block's
chain state are in that order (`ChainCertified.sorted`).


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Proofs.Routines (chainStateOf_node)

variable {V : Type}

private theorem getElem_option (f : Height → Option BlockId) (h : Height) : f[h] = f h := rfl

private theorem getElem_bool (f : Height → Bool) (h : Height) : f[h] = f h := rfl

/-! ## Lemma 92 -/

/-- When `h_F < h_j` and the record `Λ` holds at `h_j` no target other than `J`, no timeout and no
lock other than `J`, `finality_pair` returns `(h_j, J)`.

The variables:
- `Λ`: the record; `h_j`, `J`, `h_F`: the justification height, the justified root and the
  finalization height. -/
theorem finality_pair_eq_some (Λ : SigningHistory) (h_j : Height) (J : BlockId) (h_F : Height)
    -- the justification is not finalized
    (hlt : h_F < h_j)
    -- the record holds at `h_j` no target, or the target `J`
    (hTarget : Λ.target h_j = none ∨ Λ.target h_j = some J)
    -- the record holds no timeout at `h_j`
    (hTimeout : Λ.timeout h_j = false)
    -- the record holds at `h_j` no lock, or the lock `J`
    (hLock : Λ.lock h_j = none ∨ Λ.lock h_j = some J) :
    finality_pair Λ h_j J h_F = some ⟨h_j, J⟩ := by
  have h1 : ¬ h_j ≤ h_F := Nat.not_le.mpr hlt
  simp only [finality_pair, Id.run, getElem_option, getElem_bool, h1, hTimeout, if_false]
  rcases hTarget with ht | ht <;> rcases hLock with hl | hl <;> simp [ht, hl] <;> rfl

/-- **Lemma 92, the attestation carries the finality pair.** The proof; the audited statement is
in `Statements/Routines/FinalityPairStatements.lean`.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation built. -/
theorem lem92_attestation_carries_finality_pair (Λ : SigningHistory) (v : V)
    (h_c : Height) (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height)
    (a : Attestation V)
    (hSome : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a)
    (hlt : h_F < h_j) (hj : h_j < h_c)
    (hTarget : Λ.target h_j = none ∨ Λ.target h_j = some J)
    (hTimeout : Λ.timeout h_j = false)
    (hLock : Λ.lock h_j = none ∨ Λ.lock h_j = some J) :
    a.h = h_c ∧ a.finality_pair = some (FinalityPair.mk h_j J) := by
  have hfp := finality_pair_eq_some Λ h_j J h_F hlt hTarget hTimeout hLock
  simp only [create_attestation, Id.run, hfp] at hSome
  split at hSome
  · cases hSome
  · rename_i h T τ hhp
    obtain ⟨hh, -⟩ := height_pair_vote hhp
    split at hSome
    · cases hSome
    · have hle : ¬ h ≤ h_j := by rw [hh]; exact Nat.not_le.mpr hj
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some, hle, if_false] at hSome
      have ha : a = ⟨v, h, T, τ, some ⟨h_j, J⟩⟩ := (Option.some.inj hSome).symm
      subst ha
      exact ⟨hh, rfl⟩

/-! ## Counting the finality pairs -/

variable [DecidableEq V]

/-- A validator of the finality participation at `j` stays there when an attestation is counted.

The variables:
- `σ`: the chain state; `a`: the attestation counted; `j`: the height; `v`: the validator. -/
theorem process_attestation_finality_mono (σ : ChainState V) (a : Attestation V) (j : Height)
    (v : V)
    -- `v` is in the finality participation at `j` before `a` is counted
    (hv : v ∈ σ.finality_participation j) :
    v ∈ (process_attestation σ a).finality_participation j := by
  simp only [process_attestation, Id.run]
  split_ifs with h1 h2 <;> first
    | exact hv
    | skip
  all_goals
    change v ∈ Function.update σ.finality_participation (a.finality_pair.value h1).hf
      (σ.finality_participation (a.finality_pair.value h1).hf ∪ {a.val_index}) j
    rw [Function.update_apply]
    split_ifs with hj
    · subst hj; exact Finset.mem_union_left _ hv
    · exact hv

/-- Counting an attestation whose finality pair `p` names a pending justification adds its
validator to the finality participation at `p.hf`.

The variables:
- `σ`: the chain state; `a`: the attestation counted; `p`: its finality pair. -/
theorem process_attestation_finality_add (σ : ChainState V) (a : Attestation V)
    (p : FinalityPair)
    -- `a`'s finality pair is `p`
    (hp : a.finality_pair = some p)
    -- `p` names a pending justification of `σ`
    (hpend : is_pending σ p = true) :
    a.val_index ∈ (process_attestation σ a).finality_participation p.hf := by
  have h1 : a.finality_pair ≠ none := by rw [hp]; exact Option.some_ne_none p
  have hval : a.finality_pair.value h1 = p := value_eq_of_eq_some hp h1
  simp only [process_attestation, Id.run, hval, hpend, if_true]
  split_ifs
  all_goals
    change a.val_index ∈ Function.update σ.finality_participation p.hf
      (σ.finality_participation p.hf ∪ {a.val_index}) p.hf
    rw [Function.update_self]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- When a pending justification of `σ` has the height `j` and a block with the root `Tr`, and
every member of `Q` is in the finality participation at `j` or has an attestation of `atts` with
the finality pair `(j, Tr)`, every member of `Q` is in the finality participation at `j` after the
fold of `process_attestation` over `atts`.

The variables:
- `j`: the height; `Tr`: the root; `Q`: the validators; `atts`: the attestations counted;
- `σ`: the chain state the fold starts from. -/
theorem foldl_finality_participation (j : Height) (Tr : BlockId) (Q : Finset V)
    (atts : List (Attestation V)) (σ : ChainState V)
    -- a pending justification of `σ` is at `j`, with a block whose root is `Tr`
    (hpend : ∃ e ∈ σ.pending_finality, e.j = j ∧ e.T.root = Tr)
    -- every member of `Q` is counted at `j`, or has an attestation of `atts` with the pair
    -- `(j, Tr)`
    (hQ : ∀ v ∈ Q, v ∈ σ.finality_participation j ∨
      ∃ a ∈ atts, a.val_index = v ∧ a.finality_pair = some (FinalityPair.mk j Tr)) :
    ∀ v ∈ Q, v ∈ (atts.foldl process_attestation σ).finality_participation j := by
  induction atts generalizing σ with
  | nil =>
      intro v hv
      rcases hQ v hv with h | ⟨a, ha, -⟩
      · exact h
      · exact absurd ha List.not_mem_nil
  | cons a atts ih =>
      rw [List.foldl_cons]
      obtain ⟨tp, pr, fp, heq, -⟩ := process_attestation_eq σ a
      have hpend' : (process_attestation σ a).pending_finality = σ.pending_finality := by
        rw [heq]
      refine ih _ (hpend' ▸ hpend) (fun v hv => ?_)
      rcases hQ v hv with h | ⟨a', ha', hav, hafp⟩
      · exact Or.inl (process_attestation_finality_mono σ a j v h)
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · left
          have hp : is_pending σ (FinalityPair.mk j Tr) = true := by
            simp only [is_pending, decide_eq_true_eq]
            exact hpend
          have := process_attestation_finality_add σ a' _ hafp hp
          rw [hav] at this
          exact this
        · exact Or.inr ⟨a', ha', hav, hafp⟩

variable [Fintype V]

omit [DecidableEq V] in
/-- The loop over the pending justifications `l` of `process_height_events`, from the chain state
`σ`, writes only `F` and `h_F`; the height `h_F'` it leaves is `σ.h_F` or the height of an element
of `l` whose finality participation is a quorum; and, when the heights of `l` are strictly
increasing, `h_F'` is at least the height of every element of `l` whose finality participation is
a quorum.

The variables:
- `l`: the pending justifications walked; `σ`: the chain state the loop starts from. -/
theorem pending_loop (l : List (PendingPair V))
    -- the heights of `l` are strictly increasing
    (hl : l.Pairwise (fun e e' => e.j < e'.j))
    (σ : ChainState V) :
    ∃ (F' : Block V) (h_F' : Height),
      forIn (m := Id) l σ (fun (e : PendingPair V) (r : ChainState V) =>
        if quorum V ≤ r.finality_participation[e.j].card then
          pure (ForInStep.yield { r with F := e.T, h_F := e.j })
        else pure (ForInStep.yield r)) = (pure { σ with F := F', h_F := h_F' } : Id (ChainState V)) ∧
      (h_F' = σ.h_F ∨ ∃ e ∈ l, quorum V ≤ (σ.finality_participation e.j).card ∧ h_F' = e.j) ∧
      ∀ e ∈ l, quorum V ≤ (σ.finality_participation e.j).card → e.j ≤ h_F' := by
  induction l generalizing σ with
  | nil => exact ⟨σ.F, σ.h_F, rfl, Or.inl rfl, fun e he => absurd he List.not_mem_nil⟩
  | cons e l ih =>
      rw [List.pairwise_cons] at hl
      rw [List.forIn_cons]
      by_cases hq : quorum V ≤ (σ.finality_participation e.j).card
      · obtain ⟨F'', h'', heq, hor, hge⟩ := ih hl.2 { σ with F := e.T, h_F := e.j }
        refine ⟨F'', h'', ?_, ?_, ?_⟩
        · have hq' : quorum V ≤ σ.finality_participation[e.j].card := hq
          simp only [hq', if_true]
          exact heq
        · rcases hor with h | ⟨e', he', hq'', h⟩
          · exact Or.inr ⟨e, List.mem_cons_self, hq, h⟩
          · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hq'', h⟩
        · intro e' he' hq'
          rcases List.mem_cons.mp he' with rfl | he'
          · rcases hor with h | ⟨e'', he'', -, h⟩
            · exact le_of_eq h.symm
            · have := hl.1 e'' he''; rw [h]; exact le_of_lt this
          · exact hge e' he' hq'
      · obtain ⟨F'', h'', heq, hor, hge⟩ := ih hl.2 σ
        refine ⟨F'', h'', ?_, ?_, ?_⟩
        · have hq' : ¬ quorum V ≤ σ.finality_participation[e.j].card := hq
          simp only [hq', if_false]
          exact heq
        · rcases hor with h | ⟨e', he', hq'', h⟩
          · exact Or.inl h
          · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hq'', h⟩
        · intro e' he' hq'
          rcases List.mem_cons.mp he' with rfl | he'
          · exact absurd hq' hq
          · exact hge e' he' hq'

omit [DecidableEq V] in
/-- When the pending justifications of `σ` are in strictly increasing order of heights, the
height events leave a finalization height at least the height of every pending justification
whose finality participation is a quorum.

The variables:
- `C`: the parameters; `σ`: the chain state; `e`: the pending justification. -/
theorem process_height_events_h_F_ge (C : Config) (σ : ChainState V)
    -- the pending justifications are in strictly increasing order of heights
    (hs : σ.pending_finality.Pairwise (fun e e' => e.j < e'.j))
    (e : PendingPair V)
    -- `e` is a pending justification of `σ`
    (he : e ∈ σ.pending_finality)
    -- its finality participation is a quorum
    (hq : quorum V ≤ (σ.finality_participation e.j).card) :
    e.j ≤ (process_height_events C σ).h_F := by
  obtain ⟨F', h_F', hu, -, hge⟩ := pending_loop σ.pending_finality hs σ
  have key := hge e he hq
  simp only [process_height_events, Id.run]
  rw [hu, pure_bind]
  split_ifs <;> exact key

/-! ## Lemma 93 -/

/-- **Lemma 93, a block including a quorum of finality pairs finalizes the pair.** The proof; the
audited statement is in `Statements/Routines/FinalityPairStatements.lean`.

The variables:
- `C`: the parameters; `B`: the block; `H'`: its parent; `j`: the pending height; `T`: the
  pending block; `Q`: the quorum. -/
theorem lem93_block_finalizes_pending (C : Config) (B H' : Block V) (j : Height) (T : Block V)
    (Q : Finset V)
    (hParent : B.parent = H')
    (hPending : ∃ e ∈ (chainStateOf C H').pending_finality, e.j = j ∧ e.T = T)
    (hQ : quorum V ≤ |Q|)
    (hAtts : ∀ v ∈ Q, v ∈ (chainStateOf C H').finality_participation j ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.finality_pair = some (FinalityPair.mk j T.root)) :
    j ≤ (chainStateOf C B).h_F := by
  cases B with
  | genesis =>
      -- the genesis block is its own parent, and its chain state has nothing pending
      change Block.genesis = H' at hParent
      subst hParent
      obtain ⟨e, he, -⟩ := hPending
      exact absurd he List.not_mem_nil
  | node p s r votes support ats v =>
      change p = H' at hParent
      subst hParent
      obtain ⟨e, he, hej, heT⟩ := hPending
      have hsorted := (chainCertified_chainStateOf C p).sorted
      obtain ⟨tp, pr, fp, heq, -⟩ := process_attestations_eq (chainStateOf C p)
        (.node p s r votes support ats v) (Block.node p s r votes support ats v).attestations
      -- the fold over the block's attestations counts the quorum at `j`
      have hfold := foldl_finality_participation j T.root Q ats
        { chainStateOf C p with s := s } ⟨e, he, hej, by rw [heT]⟩ hAtts
      have hfp : (process_attestations (chainStateOf C p) (.node p s r votes support ats v)
          ats).finality_participation j =
          (ats.foldl process_attestation
            { chainStateOf C p with s := s }).finality_participation j := by
        rw [process_attestations_eq_foldl]; rfl
      rw [chainStateOf_node, state_transition_eq]
      have hsub : Q ⊆ (process_attestations (chainStateOf C p) (.node p s r votes support ats v)
          ats).finality_participation j := by
        intro v hv; rw [hfp]; exact hfold v hv
      have hpend : (process_attestations (chainStateOf C p) (.node p s r votes support ats v)
          ats).pending_finality = (chainStateOf C p).pending_finality := by
        have heq' := heq
        change process_attestations _ _ ats = _ at heq'
        rw [heq']
      -- the height events finalize at a height at least `j`
      have hle := process_height_events_h_F_ge C _ (hpend ▸ hsorted) e (hpend ▸ he)
        (le_trans hQ (hej ▸ Finset.card_le_card hsub))
      rw [← hej]
      exact hle

end GoldilocksCorrectness.Proofs.Routines
