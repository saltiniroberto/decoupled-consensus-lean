module
public import GoldilocksCorrectness.Record.TickFacts3
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Record.ReaderGoldilocks
public import GoldilocksCorrectness.Record.TickGoldilocks2
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefsGoldilocks
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.FinalityPairStatements
public import GoldilocksCorrectness.Proofs.Routines.Lemma14
public import GoldilocksCorrectness.Proofs.Routines.Lemma19
public import GoldilocksCorrectness.Proofs.Routines.NodeTick
public import GoldilocksCorrectness.Proofs.Routines.Record
public import GoldilocksCorrectness.Proofs.Routines.WalkEndBridge
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
import all Goldilocks.Config
import all Goldilocks.Node
import all Goldilocks.AC.Interface
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.State
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# The spec's tick facts, part 3

`tickFacts3_goldilocks`: the spec's model satisfies `TickFacts3`. At `Model.goldilocks` the tick's
outcomes are those of the spec's duty `Goldilocks.tick`, and:

- T5 is Lemma 14 (`lem14_tick_vote_walk`), with the Goldfish fork choice turned into the walk
  predicate at the Goldilocks tie-break (`goldfish_fork_choice_eq_ok_iff_walkEnd`, under the node
  invariant's clause that no two blocks of the frame's tree share a root), the landed counted sets
  into the record's (`goldilocks_countedVotes`), the voter's tree into `VoterTree`
  (`mem_voter_block_tree_iff_at`), the anchor of the revocation's answer into `AnchorAt` over the
  tick's lock entries (`get_anchor_eq_anchorAt`), and the wake condition read off the vote duty's
  test (`tick_walk`);
- T7 is Lemma 19 (`lem19_tick_proposes`), with the wake condition read off the proposal's test
  (`tick_block_awake`);
- T8 and T8b are Lemmas 49 and 49b, with the answer of `ac_to_fg` read through its body
  (`ac_to_fg_eq_ok_facts`), the votes and stamps of the tick's answer equal to the node's at the
  action time (`tick_keepsVotes_actionTime`: the tick of the available chain revokes no lock and
  sends no vote there, the proposal does not run, the attestation duty keeps the AC state), the
  stored chain states of the source and the head the computed ones (the node invariant), and the
  validator client's answer read as `AttestationFrom` (`create_attestation_some_cases`);
- Lemmas 50 and 92 are the landed ones, through `create_attestation_snd_eq_some_iff`.

The page also holds `get_anchor_eq_anchorAt`, for every model whose reader facts hold: the anchor of
a node state is `AnchorAt` over its frame with its lock entries.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (WalkStep WalkEnd RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor AwakeForProposal ResolvesAt
  AnchorAt LockedViableBlocks VoterTree HeadOf PoolHeadOf AttestationFrom AttestationRecorded VoterTreeAt
  goldilocks_countedVotes goldilocks_resolvesAt)
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBEmits DREBRel KeepsVotes
  goldilocksTieBreak)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The anchor as `AnchorAt`, for every model -/

omit [Fintype V] in
/-- Two `if`s on the deepest block of two equal sets, with the same fallback, are equal.

The variables:
- `S₁`, `S₂`: the sets; `d`: the fallback.

Read aloud: the deepest block of a set, or a fallback, depends only on the set. -/
theorem dite_deepest_congr [RootOrder] {S₁ S₂ : Finset (Block V)} (h : S₁ = S₂) (d : Block V) :
    (if h1 : Block.deepest? S₁ ≠ none then (Block.deepest? S₁).value h1 else d) =
      (if h2 : Block.deepest? S₂ ≠ none then (Block.deepest? S₂).value h2 else d) := by
  subst h
  rfl

/-- The anchor of a node state is `AnchorAt` over its frame with its lock entries, for a model whose
reader facts hold.

Why: the reader fact `get_anchor_eq`, with `is_locked_eq` and `is_live_eq`.

The variables:
- `M`: the model; `R`: its reader facts; `n`: the node state; `t`: the time.

Read aloud: the anchor of `n` at `t` is the anchor over `n`'s frame with `n`'s lock entries. -/
theorem get_anchor_eq_anchorAt [RootOrder] {M : GoldilocksModel V} (R : ReaderFacts M) (n : M.N)
    (t : Time) : M.get_anchor n t = AnchorAt M (M.fg_to_ac n) n.lockEntries t := by
  rw [R.get_anchor_eq]
  unfold AnchorAt
  refine dite_deepest_congr ?_ _
  ext B
  simp only [LockedViableBlocks, Finset.mem_filter, R.is_locked_eq, R.is_live_eq, decide_eq_true_eq,
    Bool.and_eq_true]
  constructor
  · rintro ⟨hB, e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨hB, e, he, h1, h2, h3⟩
  · rintro ⟨hB, e, he, h1, h2, h3⟩
    exact ⟨hB, e, he, ⟨h1, h2⟩, h3⟩

/-- At the spec's model, the anchor `get_anchor A Φ t` of any AC state `A` over the frame of an FG
state `S` is `AnchorAt` over that frame with `A`'s lock entries.

The variables:
- `A`: the AC state; `n`: a node state, whose FG state gives the frame; `t`: the time.

Read aloud: the spec's anchor is the anchor over the frame with the AC state's lock entries. -/
theorem goldilocks_get_anchor_eq_anchorAt [RootOrder] (A : ACState V) (n : NodeState V)
    (t : Time) :
    get_anchor A (fg_to_ac n.S) t =
      AnchorAt (Model.goldilocks (V := V)) (fg_to_ac n.S) A.lock_entries t :=
  get_anchor_eq_anchorAt (M := Model.goldilocks) readerFacts_goldilocks { n with A := A } t

/-! ## The times -/

/-- The action time of the round of the slot of `t` is not the vote time of that slot.

Why: `4 Δ b + 6 Δ = 4 Δ s + Δ` would give `4 b + 6 = 4 s + 1`.

The variables:
- `C`: the configuration; `t`: the time.

Read aloud: no time is both an action time and a vote time. -/
theorem actionTime_ne_voteTime (C : Config) (t : Time) (h : t = C.a_ (C.round (C.slot t))) :
    t ≠ C.t_ (C.slot t) + C.Δ := by
  intro h'
  have e := h.symm.trans h'
  simp only [Config.t_, Config.a_, Config.T_] at e
  generalize ((C.round (C.slot t) * C.R : ℕ) : Int) = b at e
  generalize ((C.slot t : ℕ) : Int) = a at e
  have e1 : 4 * C.Δ * b + 6 * C.Δ = C.Δ * (4 * b + 6) := by
    rw [Int.mul_add, Int.mul_comm 6 C.Δ, Int.mul_comm 4 C.Δ, Int.mul_assoc]
  have e2 : 4 * C.Δ * a + C.Δ = C.Δ * (4 * a + 1) := by
    rw [Int.mul_add, Int.mul_one, Int.mul_comm 4 C.Δ, Int.mul_assoc]
  rw [e1, e2] at e
  have h3 := Int.eq_of_mul_eq_mul_left (ne_of_gt C.Δ_pos) e
  omega

/-- The duty window of the slot of `t` starts before `t` when `t` is the action time of that
slot's round.

Why: the action time is not negative, so the start of its slot is at most it, and the duty window
starts `4 · Δ · k − Δ` before that start.

The variables:
- `C`: the configuration; `t`: the time.

Read aloud: the duty window starts before the action time. -/
theorem duty_window_start_lt_actionTime (C : Config) (t : Time)
    (h : t = C.a_ (C.round (C.slot t))) : duty_window_start C (C.slot t) < t := by
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  have hk2 : (2 : Int) ≤ (C.k : Int) := by exact_mod_cast C.k_ge_two
  have h4 : (0 : Int) < 4 * C.Δ := by omega
  have ht0 : (0 : Int) ≤ t := by
    have hb : (0 : Int) ≤ ((C.round (C.slot t) * C.R : ℕ) : Int) := Int.natCast_nonneg _
    rw [h]
    simp only [Config.a_, Config.T_, Config.t_]
    exact Int.add_nonneg (Int.mul_nonneg (le_of_lt h4) hb) (by omega)
  have hs : C.t_ (C.slot t) ≤ t := by
    simp only [Config.t_, Config.slot]
    rw [Int.fdiv_eq_ediv_of_nonneg t (le_of_lt h4),
      Int.toNat_of_nonneg (Int.ediv_nonneg ht0 (le_of_lt h4))]
    exact Int.mul_ediv_self_le (ne_of_gt h4)
  have hm : @LE.le Int _ (4 * C.Δ * 2) (4 * C.Δ * (C.k : Int)) :=
    Int.mul_le_mul_of_nonneg_left hk2 (le_of_lt h4)
  have hs' : @LE.le Int _ (C.t_ (C.slot t)) t := hs
  have e1 : @Eq Int (duty_window_start C (C.slot t))
      (C.t_ (C.slot t) + C.Δ - 4 * C.Δ * (C.k : Int)) := rfl
  show @LT.lt Int _ (duty_window_start C (C.slot t)) t
  rw [e1]
  omega

/-- The proposal window of a slot starts before the slot's start.

The variables:
- `C`: the configuration; `t`: the time.

Read aloud: the proposal window starts before the slot does. -/
theorem proposal_window_start_lt_slotStart (C : Config) (t : Time) (h : t = C.t_ (C.slot t)) :
    proposal_window_start C (C.slot t) < t := by
  have hΔ : (0 : Int) < C.Δ := C.Δ_pos
  have hk : (0 : Int) ≤ (C.k : Int) := Int.natCast_nonneg _
  have hm : @LE.le Int _ (4 * C.Δ * 1) (4 * C.Δ * ((C.k : Int) + 1)) :=
    Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ (C.k : Int) + 1 by omega)
      (show (0 : Int) ≤ 4 * C.Δ by omega)
  have h' : @Eq Int t (C.t_ (C.slot t)) := h
  have e1 : @Eq Int (proposal_window_start C (C.slot t))
      (C.t_ (C.slot t) + C.Δ - 4 * C.Δ * ((C.k : Int) + 1)) := rfl
  show @LT.lt Int _ (proposal_window_start C (C.slot t)) t
  rw [e1]
  omega

/-! ## The tick at the action time keeps the votes and the stamps -/

omit [Fintype V] in
/-- Away from the vote time of its slot, the tick of the available chain keeps the pool and the
stamps: it deletes lock entries, and at the support cutoff it runs the confirmation update, which
writes no vote and no stamp.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests.

Read aloud: away from the vote time, the tick of the available chain keeps the votes and the
stamps. -/
theorem ac_on_tick_keepsVotes [Fintype V] [RootOrder] (C : Config) (P : Provisional V)
    (A : ACState V) (Φ : Frame V) (t : Time) (v : V) (b b' : Bool) :
    DREBPost (ac_on_tick C P A Φ t v b b')
      (fun A₁ => t ≠ C.t_ (C.slot t) + C.Δ → KeepsVotes A A₁) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine DREBPost.bind_any (fun _ => ?_)
    refine DREBPost.bind_any (fun _ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind_any (fun _ => DREBPost.pure (fun hne => absurd hc.1 hne))
    · exact DREBPost.pure (fun hne => absurd hc.1 hne)
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBPost.bind
        (P := fun A'' => update_confirmation C P (expireLocks A t) Φ t (C.slot t) = .ok A'')
        (DREBPost.liftM (fun _ h => h)) (fun A'' hA'' => DREBPost.pure (fun _ => ?_))
      have h2 := GoldilocksCorrectness.Proofs.Routines.update_confirmation_keepsVotes C P
        (expireLocks A t) Φ t (C.slot t) A'' hA''
      exact ⟨h2.1, h2.2.1, h2.2.2⟩
    · exact DREBPost.pure (fun _ => GoldilocksCorrectness.Proofs.Routines.expireLocks_keepsVotes A t)

/-- At the action time of the round of its slot, a tick keeps the pool and the stamps of the
node's AC state: its tick of the available chain is away from the vote time, the proposal does
not run (the start of a slot is never the action time of its round), and the attestation duty
keeps the AC state.

The variables:
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `t`: the time.

Read aloud: a tick at the action time keeps the node's votes and stamps. -/
theorem tick_keepsVotes_actionTime [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (t : Time) :
    DREBPost (tick C P X n t)
      (fun n' => t = C.a_ (C.round (C.slot t)) → KeepsVotes n.A n'.A) := by
  obtain ⟨hS, hA, hv, -⟩ := GoldilocksCorrectness.Proofs.Routines.record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind (P := fun A₁ => t ≠ C.t_ (C.slot t) + C.Δ → KeepsVotes n.A A₁)
    ((ac_on_tick_keepsVotes C P _ _ t _ _ _).mono (fun A₁ h => by rw [hA] at h; exact h))
    (fun A₁ hA₁ => ?_)
  refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hstart : t = C.t_ (C.slot t) := hc.1.1.2
    exact DREBPost.bind_any (fun _ => DREBPost.ite
      (fun _ => DREBPost.bind_any (fun _ => DREBPost.pure (fun ht =>
        absurd (hstart.symm.trans ht)
          (GoldilocksCorrectness.Proofs.Routines.slotStart_ne_actionTime C _))))
      (fun _ => DREBPost.pure (fun ht => absurd (hstart.symm.trans ht)
          (GoldilocksCorrectness.Proofs.Routines.slotStart_ne_actionTime C _))))
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBPost.bind (GoldilocksCorrectness.Proofs.Routines.attest_A C _) ?_
      intro n₅ h₅
      refine DREBPost.pure (fun ht => ?_)
      rw [h₅]
      exact hA₁ (actionTime_ne_voteTime C t ht)
    · exact DREBPost.pure (fun ht => hA₁ (actionTime_ne_voteTime C t ht))

/-! ## The proposal's wake test -/

/-- Every block a tick sends was sent with the proposal's wake test passing: the proposal runs
only inside its `if`, whose condition includes the test, and the tick of the available chain and
the attestation duty send no block.

The variables:
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `t`: the time.

Read aloud: a tick proposes only when the node has been awake since the proposal window's
start. -/
theorem tick_block_awake [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (t : Time) :
    DREBEmits (fun l => ∀ B : Block V, NamedObject.block B ∈ l →
        (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true)
      (tick C P X n t) := by
  simp only [tick]
  refine (DREBEmits.bind (L₂ := fun l => ∀ B : Block V, NamedObject.block B ∈ l →
      (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true)
    (GoldilocksCorrectness.Proofs.Routines.ac_on_tick_sends C P _ _ t _ _ _)
    (fun A₁ => ?_)).mono ?_
  · refine DREBEmits.ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have hw : (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true :=
        hc.2
      refine (DREBEmits.bind (L₂ := fun _ => True)
        (GoldilocksCorrectness.Proofs.Routines.propose_block_sends C P X _)
        (fun n₄ => ?_)).mono (fun _ _ _ _ => hw)
      refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := fun _ => True)
          (GoldilocksCorrectness.Proofs.Routines.attest_sends C _)
          (fun _ => DREBEmits.pure trivial)).mono (fun _ _ => trivial)
      · exact DREBEmits.pure trivial
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := (· = []))
          (GoldilocksCorrectness.Proofs.Routines.attest_sends C _)
          (fun _ => DREBEmits.pure rfl)).mono (fun _ h B hB =>
            absurd hB (GoldilocksCorrectness.Proofs.Routines.noBlock_of_attest h B))
      · exact DREBEmits.pure (fun _ h => absurd h List.not_mem_nil)
  · rintro _ ⟨l₁, l₂, rfl, h₁, h₂⟩ B hB
    rcases List.mem_append.mp hB with hB | hB
    · obtain ⟨⟨_, heq⟩, -⟩ := h₁.2 _ hB
      cases heq
    · exact h₂ B hB

/-! ## The answer of `ac_to_fg` -/

omit [Fintype V] in
/-- What an answer `fi` of `ac_to_fg C A Φ t` holds: its source is the deepest fast block of `A`
in the viable tree of `Φ.tree`; and for a list `sv` of exactly the votes of `A`'s list of the slot
of `t` that resolve, its head is the answer of the Goldfish fork choice from the anchor of `A`
through that viable tree, counting that list and `sv`.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `t`: the time; `fi`: the answer.

Read aloud: the duty's source is the deepest fast block in the viable tree, and its head the end
of the fork choice counting the slot's votes. -/
theorem ac_to_fg_eq_ok_facts [Fintype V] [RootOrder] {C : Config} {A : ACState V} {Φ : Frame V}
    {t : Time} {fi : FGInput V} (h : ac_to_fg C A Φ t = .ok fi) :
    fi.source = Block.deepest? (A.fast_blocks ∩ viable_tree Φ Φ.tree) ∧
      ∃ sv : List (GoldfishVote V),
        (∀ vote : GoldfishVote V, vote ∈ sv ↔
          vote ∈ A.gf_votes (C.slot t) ∧ ∃ y : Stamp, A.tau Φ vote = .ok (some y)) ∧
        goldfish_fork_choice C Φ t (get_anchor A Φ t) (viable_tree Φ Φ.tree)
          (A.gf_votes (C.slot t)).toFinset sv.toFinset (C.slot t) = .ok fi.head := by
  simp only [ac_to_fg] at h
  obtain ⟨sv, hsv, h1⟩ := GoldilocksCorrectness.Proofs.Routines.ok_of_bind_eq_ok h
  obtain ⟨head, hhead, h2⟩ := GoldilocksCorrectness.Proofs.Routines.ok_of_bind_eq_ok h1
  simp only [pure, Except.pure, Except.ok.injEq] at h2
  subst h2
  refine ⟨rfl, sv, fun vote => ?_, hhead⟩
  rw [List.mem_filterM_ok_iff _ _ _ hsv vote]
  refine and_congr_right fun _ => ?_
  cases hτ : A.tau Φ vote with
  | error e => simp [bind, Except.bind]
  | ok y =>
    cases y with
    | none => simp [bind, Except.bind, pure, Except.pure]
    | some y => simp [bind, Except.bind, pure, Except.pure]

/-! ## The validator client's attestation -/

omit [DecidableEq V] [Fintype V] in
/-- What `create_attestation` builds, by cases: when the height pair is the vote at `h_c` for `T_c`
(a timeout when `τ`) and the record is not forbidden it, the record with the attestation of `v`
with that vote and the finality pair cut at `h_c` written into it, and that attestation; otherwise
the record unchanged and no attestation.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height.

Read aloud: the validator client builds the allowed vote with the finality pair cut at the vote's
height, or nothing. -/
theorem create_attestation_some_cases (Λ : SigningHistory) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) :
    (∃ τ : Bool, height_pair Λ (some (h_c, T_c)) (finality_pair Λ h_j J h_F) =
        HeightPair.vote h_c T_c τ ∧ already_sent Λ h_c T_c τ = false ∧
        create_attestation Λ v h_c T_c h_j J h_F =
          (record_attestation Λ (Attestation.mk v h_c T_c τ
            (match finality_pair Λ h_j J h_F with
              | some q => if h_c ≤ q.hf then none else some q
              | none => none)),
           some (Attestation.mk v h_c T_c τ
            (match finality_pair Λ h_j J h_F with
              | some q => if h_c ≤ q.hf then none else some q
              | none => none)))) ∨
      (create_attestation Λ v h_c T_c h_j J h_F = (Λ, none) ∧
        ∀ τ : Bool, height_pair Λ (some (h_c, T_c)) (finality_pair Λ h_j J h_F) =
          HeightPair.vote h_c T_c τ → already_sent Λ h_c T_c τ = true) := by
  cases hhp : height_pair Λ (some (h_c, T_c)) (finality_pair Λ h_j J h_F) with
  | empty =>
    right
    refine ⟨?_, fun τ h => absurd h (by simp)⟩
    simp only [create_attestation, Id.run, hhp]
    rfl
  | vote h T τ =>
    obtain ⟨rfl, rfl, -⟩ := GoldilocksCorrectness.Proofs.Routines.height_pair_vote_cases hhp
    by_cases hs : already_sent Λ h T τ = true
    · right
      refine ⟨?_, fun τ' h' => ?_⟩
      · simp only [create_attestation, Id.run, hhp, hs]
        rfl
      · obtain ⟨-, -, rfl⟩ := HeightPair.vote.inj h'
        exact hs
    · left
      have hs' : already_sent Λ h T τ = false := by simpa using hs
      refine ⟨τ, rfl, hs', ?_⟩
      cases hfp : finality_pair Λ h_j J h_F with
      | none =>
        rw [hfp] at hhp
        simp only [create_attestation, Id.run, hhp, hs', hfp, Bool.false_eq_true, ite_false,
          ne_eq, not_true_eq_false, dite_false]
        rfl
      | some q =>
        rw [hfp] at hhp
        by_cases hle : h ≤ q.hf
        · simp only [create_attestation, Id.run, hhp, hs', hfp, Bool.false_eq_true, ite_false,
            ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some, hle,
            ite_true]
          rfl
        · simp only [create_attestation, Id.run, hhp, hs', hfp, Bool.false_eq_true, ite_false,
            ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some, hle]
          rfl

/-- At the spec's model, `create_attestation` on a node's record builds `a` exactly when `a` is
`AttestationFrom` of that node state.

The variables:
- `n`: the node state; `v`: the validator; `h_c`, `T_c`, `h_j`, `J`, `h_F`: the client's inputs;
  `a`: the attestation.

Read aloud: the spec's validator client builds `a` exactly when the record says it does. -/
theorem create_attestation_snd_eq_some_iff (n : NodeState V) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V) :
    (create_attestation n.Λ v h_c T_c h_j J h_F).2 = some a ↔
      AttestationFrom (Model.goldilocks (V := V)) n v h_c T_c h_j J h_F a := by
  rcases create_attestation_some_cases n.Λ v h_c T_c h_j J h_F with
    ⟨τ, hhp, hs, he⟩ | ⟨he, hno⟩
  · rw [he]
    constructor
    · intro ha
      exact ⟨τ, hhp, hs, (Option.some.inj ha).symm⟩
    · rintro ⟨τ', hhp', hs', rfl⟩
      have hτ : τ' = τ := by
        have hhp'' : height_pair n.Λ (some (h_c, T_c)) (finality_pair n.Λ h_j J h_F) =
            HeightPair.vote h_c T_c τ' := hhp'
        rw [hhp] at hhp''
        replace hhp' := hhp''
        exact (HeightPair.vote.inj hhp').2.2.symm
      subst hτ
      rfl
  · rw [he]
    constructor
    · intro ha
      cases ha
    · rintro ⟨τ', hhp', hs', -⟩
      have := hno τ' hhp'
      exact absurd this (by
        rw [show already_sent n.Λ h_c T_c τ' = false from hs']
        simp)

omit [DecidableEq V] [Fintype V] in
/-- When `create_attestation` builds `a` on the record `Λ`, the record it returns is `Λ` with `a`
written into it.

The variables:
- `Λ`: the record; `v`, `h_c`, `T_c`, `h_j`, `J`, `h_F`: the client's inputs;
  `a`: the attestation.

Read aloud: when the client builds `a`, it records `a`. -/
theorem create_attestation_fst_of_some (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V)
    (ha : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a) :
    (create_attestation Λ v h_c T_c h_j J h_F).1 = record_attestation Λ a := by
  rcases create_attestation_some_cases Λ v h_c T_c h_j J h_F with ⟨τ, -, -, he⟩ | ⟨he, -⟩
  · rw [he] at ha ⊢
    rw [← Option.some.inj ha]
  · rw [he] at ha
    cases ha

/-- At the spec's model, a node state whose record is the record of `n` with `a` written into it
satisfies `AttestationRecorded`.

The variables:
- `n`, `n'`: the node states; `a`: the attestation.

Read aloud: writing `a` into the record is what `AttestationRecorded` says. -/
theorem attestationRecorded_of_record (n n' : NodeState V) (a : Attestation V)
    (h : n'.Λ = record_attestation n.Λ a) :
    AttestationRecorded (Model.goldilocks (V := V)) n a n' := by
  refine ⟨?_, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
  · show n'.Λ.sent = n.Λ.sent ∪ {a.content}
    rw [h, GoldilocksCorrectness.Proofs.Routines.record_attestation_sent]
  · show n'.Λ.lock hh = _
    rw [h, GoldilocksCorrectness.Proofs.Routines.record_attestation_lock]
    cases a.finality_pair with
    | none => rfl
    | some p =>
      show Function.update n.Λ.lock p.hf (some p.Tf) hh = _
      rw [Function.update_apply]
      rfl
  · show n'.Λ.target hh = _
    rw [h, GoldilocksCorrectness.Proofs.Routines.record_attestation_target]
    show _ = if a.τ = false ∧ n.Λ.target a.h = none ∧ hh = a.h then some a.T else n.Λ.target hh
    by_cases hc : a.τ = false ∧ n.Λ.target a.h = none
    · rw [if_pos hc, Function.update_apply]
      by_cases he : hh = a.h
      · rw [if_pos he, if_pos ⟨hc.1, hc.2, he⟩]
      · rw [if_neg he, if_neg (fun h' => he h'.2.2)]
    · rw [if_neg hc, if_neg (fun h' => hc ⟨h'.1, h'.2.1⟩)]
  · show n'.Λ.timeout hh = _
    rw [h, GoldilocksCorrectness.Proofs.Routines.record_attestation_timeout]
    show _ = if a.τ = true ∧ hh = a.h then true else n.Λ.timeout hh
    by_cases hc : a.τ = true
    · rw [if_pos hc, Function.update_apply]
      by_cases he : hh = a.h
      · rw [if_pos he, if_pos ⟨hc, he⟩]
      · rw [if_neg he, if_neg (fun h' => he h'.2)]
    · rw [if_neg hc, if_neg (fun h' => hc h'.1)]

/-! ## The instance -/

/-- At the spec's model, the walk of a duty from `A₀` through a subset of the frame's tree, at the
model's tie-break, is the spec's Goldfish fork choice from `A₀`, when no two blocks of the frame's
tree share a root.

The variables:
- `n`: the node state; `hRoots`: no two blocks of its frame's tree share a root;
- `C`, `t`, `A₀`, `tree`, `votes`, `sv`, `s`, `H`: the fork choice's inputs and answer.

Read aloud: the spec's fork choice through part of the frame's tree answers the walk's end. -/
theorem walkEnd_of_fork_choice [RootOrder] (n : NodeState V)
    (hRoots : RootsNameBlocksIn (fg_to_ac n.S).tree) (C : Config) (t : Time) (A₀ : Block V)
    (tree : Finset (Block V)) (htree : tree ⊆ (fg_to_ac n.S).tree)
    (votes sv : Finset (GoldfishVote V)) (s : Slot) (H : Block V)
    (h : goldfish_fork_choice C (fg_to_ac n.S) t A₀ (viable_tree (fg_to_ac n.S) tree) votes sv s =
      .ok H) :
    @WalkEnd V goldilocksTieBreak (viable_tree (fg_to_ac n.S) tree)
      (goldfish_score (fg_to_ac n.S) votes sv s) (goldfish_eligible C (fg_to_ac n.S) t votes sv s)
      A₀ H := by
  have hsub : viable_tree (fg_to_ac n.S) tree ⊆ (fg_to_ac n.S).tree := fun B hB =>
    htree ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff _ tree B).1 hB).1
  exact (GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq_ok_iff_walkEnd C
    (fg_to_ac n.S) t A₀ (viable_tree (fg_to_ac n.S) tree) votes sv s
    (GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots)).1 h

/-! ## A tick holds what it sends -/

open GoldilocksCorrectness.Proofs.Routines (DREBSpec DREPost revoke_locks_keepsVotes
  update_confirmation_keepsVotes on_attestation_pool)

omit [DecidableEq V] [Fintype V] in
/-- A relation between a routine's answer and what it appends, and a condition on what it
appends alone, hold together.

The variables:
- `R`: the relation; `L`: the condition; `m`: the routine. -/
theorem drebSpec_and_emits {α : Type} {R : α → List (NamedObject V) → Prop}
    {L : List (NamedObject V) → Prop} {m : DREB V α} (hR : DREBSpec R m) (hL : DREBEmits L m) :
    DREBSpec (fun a l => R a l ∧ L l) m := by
  intro sent₀ a sent h
  obtain ⟨l, hl, hRl⟩ := hR sent₀ a sent h
  obtain ⟨l', hl', hLl⟩ := hL sent₀ a sent h
  have e : l = l' := List.append_cancel_left (hl.symm.trans hl')
  subst e
  exact ⟨l, hl, hRl, hLl⟩

omit [DecidableEq V] [Fintype V] in
/-- A condition on what a routine appends is a relation between its answer and what it appends.

The variables:
- `L`: the condition; `m`: the routine. -/
theorem drebSpec_of_emits {α : Type} {L : List (NamedObject V) → Prop} {m : DREB V α}
    (hL : DREBEmits L m) : DREBSpec (fun _ l => L l) m :=
  fun sent₀ a sent h => hL sent₀ a sent h

omit [Fintype V] in
/-- The admission of a Goldfish vote of the slot of `t`, of a member of that slot's committee,
leaves the vote among the votes of its slot, unless the votes of that slot already held two votes
of its validator.

Why: `on_goldfish_vote` refuses such a vote only when it already holds it, or when its validator
equivocates in the votes of the slot; otherwise it appends it.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the time; `vote`: the vote.

Read aloud: an admitted own vote is held, unless its validator already equivocated. -/
theorem on_goldfish_vote_holds (C : Config) (P : Provisional V) (A : ACState V) (t : Time)
    (vote : GoldfishVote V) (hs : vote.slot = C.slot t)
    (hc : vote.val_index ∈ P.committee vote.slot) :
    vote ∈ (on_goldfish_vote C P A t vote).gf_votes vote.slot ∨
      equivocates (A.pool vote.slot) vote.val_index = true := by
  simp only [on_goldfish_vote, Id.run]
  split
  · next h =>
    left
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with ((h | h) | h) | h
    · rw [hs] at h
      exact absurd h (Nat.not_lt.2 (Nat.sub_le _ _))
    · rw [hs] at h
      exact absurd h (Nat.lt_irrefl _)
    · exact absurd hc h
    · exact h
  split
  · right
    assumption
  · left
    show vote ∈ Function.update A.gf_votes vote.slot (A.gf_votes vote.slot ++ [vote]) vote.slot
    simp

/-- The Goldfish vote duty holds the vote it sends, unless the votes of the vote's slot already
held two votes of its validator.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the validator. -/
theorem goldfish_vote_holds_sent [RootOrder] (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) :
    DREBSpec (fun A' l => ∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
        vote ∈ A'.gf_votes vote.slot ∨ equivocates (A.pool vote.slot) vote.val_index = true)
      (goldfish_vote C P A Φ t v) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBSpec.pure (fun vote h => absurd h (List.not_mem_nil))
    | refine DREBSpec.bind_liftPost (DREPost.true _) (fun _ _ => ?_)
    | refine DREBSpec.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBSpec.broadcast_pure _ (fun vote h => ?_)
  rename_i hc
  rw [List.mem_singleton] at h
  cases h
  exact on_goldfish_vote_holds C P A t _ rfl hc

/-- The tick of the available chain holds the vote it sends, unless the votes of the vote's slot
already held two votes of its validator; and it sends a vote only at the vote time of the slot of
`t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the validator; `b`, `b'`: the wake tests. -/
theorem ac_on_tick_holds_sent [RootOrder] (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (v : V) (b b' : Bool) :
    DREBSpec (fun A' l => ∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
        t = C.t_ (C.slot t) + C.Δ ∧
          (vote ∈ A'.gf_votes vote.slot ∨ equivocates (A.pool vote.slot) vote.val_index = true))
      (ac_on_tick C P A Φ t v b b') := by
  simp only [ac_on_tick]
  refine DREBSpec.ite (fun hc => ?_) (fun _ => ?_)
  · have ht : t = C.t_ (C.slot t) + C.Δ := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    refine DREBSpec.bind_liftPost (revoke_locks_keepsVotes P _ Φ t _) (fun A₂ h₂ => ?_)
    have hpool : ∀ s : Slot, A₂.pool s = A.pool s := fun s => by
      simp only [ACState.pool, h₂.1]
    refine DREBSpec.bind' (goldfish_vote_holds_sent C P A₂ Φ t v) (fun A₃ l₁ h₁ => ?_)
    have h₃ : ∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l₁ ++ [] →
        t = C.t_ (C.slot t) + C.Δ ∧
          (vote ∈ A₃.gf_votes vote.slot ∨ equivocates (A.pool vote.slot) vote.val_index = true) :=
      fun vote h => by
        rw [List.append_nil] at h
        rw [← hpool]
        exact ⟨ht, h₁ vote h⟩
    refine DREBSpec.ite (fun _ => ?_) (fun _ => DREBSpec.pure h₃)
    exact DREBSpec.bind_liftPost (update_confirmation_keepsVotes C P _ Φ t _)
      (fun A₄ h₄ => DREBSpec.pure (fun vote h => by
        rw [h₄.1]
        exact h₃ vote h))
  · refine DREBSpec.ite (fun _ => ?_) (fun _ => DREBSpec.pure (fun vote h => absurd h List.not_mem_nil))
    exact DREBSpec.bind_liftPost (update_confirmation_keepsVotes C P _ Φ t _)
      (fun A₄ _ => DREBSpec.pure (fun vote h => absurd h List.not_mem_nil))

/-- The attestation duty holds the attestation it sends, when that attestation is well formed.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_holds_sent [RootOrder] (C : Config) (n : NodeState V) :
    DREBSpec (fun n' l => ∀ a : Attestation V, NamedObject.attest a ∈ l →
        attestation_well_formed a = true → a ∈ n'.S.attestations) (attest C n) := by
  simp only [attest]
  refine DREBSpec.bind_liftPost (DREPost.true _) (fun fi _ => ?_)
  obtain ⟨src?, head⟩ := fi
  cases src? with
  | none =>
      simp only [ne_eq, not_true_eq_false, dite_false]
      exact DREBSpec.pure (fun a h => absurd h List.not_mem_nil)
  | some source =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
      split
      · refine DREBSpec.broadcast_pure _ (fun a h hwf => ?_)
        rw [List.mem_singleton] at h
        cases h
        exact (on_attestation_pool _ _).2 hwf
      · exact DREBSpec.pure (fun a h => absurd h List.not_mem_nil)

/-- The node's tick holds the Goldfish vote it sends, unless the node's votes of the vote's slot
already held two votes of its validator, and holds the well-formed attestation it sends.

Why: a vote is sent only at the vote time of the slot of `t` (`ac_on_tick_holds_sent`), where
neither the proposal (it runs at the slot's start) nor the attestation duty (at the round's action
time) runs, so the tick's answer has the votes the tick of the available chain left; the
attestation duty is the tick's last step and holds the attestation it sends.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_holds_sent_rel [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBSpec (fun n' l =>
        (∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ l →
          vote ∈ n'.A.gf_votes vote.slot ∨ equivocates (n.A.pool vote.slot) vote.val_index = true) ∧
        (∀ a : Attestation V, NamedObject.attest a ∈ l →
          attestation_well_formed a = true → a ∈ n'.S.attestations))
      (tick C P X n t) := by
  obtain ⟨-, hA, -, -⟩ := GoldilocksCorrectness.Proofs.Routines.record_awake_frame n t
  simp only [tick]
  refine DREBSpec.bind' (drebSpec_and_emits (ac_on_tick_holds_sent C P _ _ t _ _ _)
    (GoldilocksCorrectness.Proofs.Routines.ac_on_tick_sends C P _ _ t _ _ _)) (fun A₁ l₁ h₁ => ?_)
  obtain ⟨hv₁, -, hl₁⟩ := h₁
  rw [hA] at hv₁
  -- the tick of the available chain sends only votes, at the vote time
  have hnoatt : ∀ a : Attestation V, NamedObject.attest a ∉ l₁ := fun a h => by
    obtain ⟨⟨_, he⟩, -⟩ := hl₁ _ h
    cases he
  -- at a time that is not the vote time, it sends no vote
  have hnovote : t ≠ C.t_ (C.slot t) + C.Δ → ∀ vote : GoldfishVote V,
      NamedObject.gfVote vote ∉ l₁ := fun hne vote h => hne (hv₁ vote h).1
  refine DREBSpec.ite (fun hc₁ => ?_) (fun _ => ?_)
  · -- the proposal ran, at the start of the slot: no vote was sent, and the attestation duty
    -- does not run
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₁
    have hstart : t = C.t_ (C.slot t) := hc₁.1.1.2
    have hne : t ≠ C.t_ (C.slot t) + C.Δ := fun h =>
      ne_of_lt C.Δ_pos (Int.add_left_cancel ((Int.add_zero _).trans (hstart.symm.trans h)))
    refine DREBSpec.bind' (drebSpec_of_emits
      (GoldilocksCorrectness.Proofs.Routines.propose_block_sends C P X _)) (fun n₄ l₂ h₂ => ?_)
    obtain ⟨B, rfl⟩ := h₂
    refine DREBSpec.ite (fun hc₂ => ?_) (fun _ => DREBSpec.pure ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      exact absurd (hstart.symm.trans hc₂.1)
        (GoldilocksCorrectness.Proofs.Routines.slotStart_ne_actionTime C _)
    · refine ⟨fun vote h => ?_, fun a h => ?_⟩
      · simp only [List.append_nil, List.mem_append, List.mem_singleton, reduceCtorEq,
          or_false] at h
        exact absurd h (hnovote hne vote)
      · simp only [List.append_nil, List.mem_append, List.mem_singleton, reduceCtorEq,
          or_false] at h
        exact absurd h (hnoatt a)
  · refine DREBSpec.ite (fun hc₂ => ?_) (fun _ => DREBSpec.pure ?_)
    · -- the attestation duty ran, at the action time: no vote was sent, and the duty sends
      -- attestations only
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc₂
      have hne : t ≠ C.t_ (C.slot t) + C.Δ := actionTime_ne_voteTime C t hc₂.1
      refine DREBSpec.bind' (drebSpec_and_emits (attest_holds_sent C _)
        (GoldilocksCorrectness.Proofs.Routines.attest_sends C _)) (fun n₅ l₂ h₂ => DREBSpec.pure ?_)
      refine ⟨fun vote h => ?_, fun a h hwf => ?_⟩
      · simp only [List.append_nil, List.mem_append] at h
        rcases h with h | h
        · exact absurd h (hnovote hne vote)
        · rcases h₂.2 with he | ⟨a', he⟩ <;> rw [he] at h <;> simp at h
      · simp only [List.append_nil, List.mem_append] at h
        rcases h with h | h
        · exact absurd h (hnoatt a)
        · exact h₂.1 a h hwf
    · -- nothing else ran: the answer has the votes the tick of the available chain left
      refine ⟨fun vote h => ?_, fun a h => ?_⟩
      · rw [List.append_nil] at h
        exact (hv₁ vote h).2
      · rw [List.append_nil] at h
        exact absurd h (hnoatt a)

/-- The spec's model satisfies the facts of the tick, part 3.

Read aloud: the spec's tick votes, proposes and attests as the record says, and its validator
client builds what the record says. -/
theorem tickFacts3_goldilocks : TickFacts3 (Model.goldilocks (V := V)) where
  tick_vote_head := by
    intro _ C P X n t n' sent vote hRun hInv hVote
    obtain ⟨ht, hv, hs, hcomm, A', votes, sv, vbt, H, -, hCV, hvbt, hfc, hhead, hlock⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk C P X n n' t sent vote hRun
        hVote
    have hRoots := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hInv.1
    have hb := ((GoldilocksCorrectness.Proofs.Routines.tick_walk C P X n t).of_outcome hRun
      vote hVote).1
    have hVT : VoterTree (Model.goldilocks (V := V)) C n (C.slot t) = vbt := by
      ext B
      simp only [VoterTree, Finset.mem_filter]
      rw [GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at C n.A
          (fg_to_ac n.S) (C.slot t) vbt hvbt B]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    have hsub : vbt ⊆ (fg_to_ac n.S).tree := fun B hB =>
      ((GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at C n.A
        (fg_to_ac n.S) (C.slot t) vbt hvbt B).1 hB).1
    have hAnc : AnchorAt (Model.goldilocks (V := V)) (fg_to_ac n.S) n'.A.lock_entries t =
        get_anchor A' (fg_to_ac n.S) t := by
      rw [hlock]
      exact (goldilocks_get_anchor_eq_anchorAt A' n t).symm
    refine ⟨ht, hv, hs, hcomm,
      GoldilocksCorrectness.Proofs.Routines.awakeSince_of_record_awake hb
        (duty_window_start_lt_of_dutyTime C t (Or.inl ht)),
      H, ⟨votes, sv, (goldilocks_countedVotes C n (C.slot t) votes sv hRoots).1 hCV, ?_⟩, hhead⟩
    show @WalkEnd V goldilocksTieBreak
      (viable_tree (fg_to_ac n.S) (VoterTree (Model.goldilocks (V := V)) C n (C.slot t)))
      (goldfish_score (fg_to_ac n.S) votes sv (C.slot t - 1))
      (goldfish_eligible C (fg_to_ac n.S) t votes sv (C.slot t - 1))
      (AnchorAt (Model.goldilocks (V := V)) (fg_to_ac n.S) n'.A.lock_entries t) H
    rw [hVT, hAnc]
    exact walkEnd_of_fork_choice n hRoots C t _ vbt hsub votes sv _ H hfc
  tick_proposal := by
    intro _ C P X n t n' sent B hRun hInv hB
    obtain ⟨hpos, ht, hprop, H, votes, sv, hvotes, hsv, hfc, hBeq⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes C P X n n' t sent B hRun hB
    have hRoots := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hInv.1
    have hw := (tick_block_awake C P X n t).of_outcome hRun B hB
    have hres : ∀ vote : GoldfishVote V, (∃ y : Stamp, n.A.tau (fg_to_ac n.S) vote = .ok (some y))
        ↔ ∃ y : Stamp, ResolvesAt (Model.goldilocks (V := V)) n vote y :=
      fun vote => exists_congr (fun y => goldilocks_resolvesAt n vote y hRoots)
    refine ⟨hpos, ht, hprop,
      GoldilocksCorrectness.Proofs.Routines.awakeSince_of_record_awake hw
        (proposal_window_start_lt_slotStart C t ht),
      H, votes, sv, hvotes, fun vote => by rw [hsv vote, hres vote], ⟨votes.toFinset,
        sv.toFinset, ⟨by rw [hvotes]; rfl, fun vote => ?_⟩, ?_⟩, hBeq⟩
    · show vote ∈ sv.toFinset ↔ vote ∈ (n.A.gf_votes (C.slot t - 1)).toFinset ∧
        ∃ y : Stamp, ResolvesAt (Model.goldilocks (V := V)) n vote y
      rw [List.mem_toFinset, List.mem_toFinset, hsv vote, hres vote, hvotes]
    · show @WalkEnd V goldilocksTieBreak (viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree)
        (goldfish_score (fg_to_ac n.S) votes.toFinset sv.toFinset (C.slot t - 1))
        (goldfish_eligible C (fg_to_ac n.S) t votes.toFinset sv.toFinset (C.slot t - 1))
        (get_anchor n.A (fg_to_ac n.S) t) H
      exact walkEnd_of_fork_choice n hRoots C t _ _ (Finset.Subset.refl _) _ _ _ H hfc
  tick_attestation := by
    intro _ C P X n t n' sent a hRun hInv hA
    obtain ⟨hact, fi, source, hfi, hs, hbuilt, hΛ⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem49_tick_attests C P X n n' t sent a hRun hA
    have hRoots := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hInv.1
    have hw := (GoldilocksCorrectness.Proofs.Routines.tick_attest_awake C P X n t).of_outcome
      hRun a hA
    have hkv : KeepsVotes n.A n'.A := (tick_keepsVotes_actionTime C P X n t).of_outcome hRun hact
    obtain ⟨hsrc, sv, hsv, hfc⟩ := ac_to_fg_eq_ok_facts hfi
    -- the source and the head are blocks of the tree, whose stored chain states are computed
    have hsT : source ∈ n.S.T := by
      have h1 : source ∈ n'.A.fast_blocks ∩ viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree :=
        GoldilocksCorrectness.Proofs.Routines.deepest?_mem (hsrc.symm.trans hs)
      have h2 := ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff _ _ _).1
        (Finset.mem_inter.1 h1).2).1
      exact ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree n.S source).1 h2).1
    have hhT : fi.head ∈ n.S.T :=
      (GoldilocksCorrectness.Proofs.Routines.ac_to_fg_head_mem C n'.A n.S t hInv.1.2.2.2.1
        hInv.1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1 hInv.1.2.2.2.2.2.2.2.2.2.1.2.1.1 fi hfi).1
    have hσs := hInv.1.2.2.2.2.2.1 source hsT
    have hσh := hInv.1.2.2.2.2.2.1 fi.head hhT
    rw [hσs, hσh] at hbuilt hΛ
    refine ⟨hact, GoldilocksCorrectness.Proofs.Routines.awakeSince_of_record_awake hw
        (duty_window_start_lt_actionTime C t hact), source, fi.head, hsrc.symm.trans hs,
      ⟨n.A.pool (C.slot t), sv.toFinset, ⟨rfl, fun vote => ?_⟩, ?_⟩,
      (create_attestation_snd_eq_some_iff n _ _ _ _ _ _ a).1 hbuilt,
      attestationRecorded_of_record n n' a
        (hΛ.trans (create_attestation_fst_of_some _ _ _ _ _ _ _ a hbuilt))⟩
    · rw [List.mem_toFinset, hsv vote]
      show vote ∈ n'.A.gf_votes (C.slot t) ∧ _ ↔ vote ∈ (n.A.gf_votes (C.slot t)).toFinset ∧ _
      rw [hkv.1, List.mem_toFinset, GoldilocksCorrectness.Proofs.Routines.tau_of_keepsVotes hkv]
      exact and_congr_right (fun _ => exists_congr (fun y => goldilocks_resolvesAt n vote y hRoots))
    · have hpool : (n'.A.gf_votes (C.slot t)).toFinset = n.A.pool (C.slot t) := by
        rw [hkv.1]
        rfl
      rw [hpool, goldilocks_get_anchor_eq_anchorAt] at hfc
      show @WalkEnd V goldilocksTieBreak (viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree)
        (goldfish_score (fg_to_ac n.S) (n.A.pool (C.slot t)) sv.toFinset (C.slot t))
        (goldfish_eligible C (fg_to_ac n.S) t (n.A.pool (C.slot t)) sv.toFinset (C.slot t))
        (AnchorAt (Model.goldilocks (V := V)) (fg_to_ac n.S) n'.A.lock_entries t) fi.head
      exact walkEnd_of_fork_choice n hRoots C t _ _ (Finset.Subset.refl _) _ _ _ _ hfc
  tick_attestation_sent := by
    intro _ C P X n t n' sent a source head hRun hInv hact hAw hsrc hhead hfrom
    have hRoots := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hInv.1
    obtain ⟨τ, hτ, hle⟩ := hAw
    have hkv : KeepsVotes n.A n'.A := (tick_keepsVotes_actionTime C P X n t).of_outcome hRun hact
    obtain ⟨fi, hfi⟩ := (GoldilocksCorrectness.Proofs.Routines.tick_attest_input C P X n t).of_outcome
      hRun hact (GoldilocksCorrectness.Proofs.Routines.awake_since_record_awake hτ hle)
    obtain ⟨hsrc', sv, hsv, hfc⟩ := ac_to_fg_eq_ok_facts hfi
    have hs : fi.source = some source := hsrc'.trans hsrc
    -- the head the duty computes is `head`: both are the end of one walk
    obtain ⟨votes, sv', ⟨hvotes, hsv'⟩, hW⟩ := hhead
    have hpool : (n'.A.gf_votes (C.slot t)).toFinset = votes := by
      rw [hkv.1, hvotes]
      rfl
    have hsvs : sv.toFinset = sv' := by
      ext vote
      rw [List.mem_toFinset, hsv vote, hsv' vote]
      show vote ∈ n'.A.gf_votes (C.slot t) ∧ _ ↔ vote ∈ (n.A.gf_votes (C.slot t)).toFinset ∧ _
      rw [hkv.1, List.mem_toFinset, GoldilocksCorrectness.Proofs.Routines.tau_of_keepsVotes hkv]
      exact and_congr_right (fun _ => exists_congr (fun y => goldilocks_resolvesAt n vote y hRoots))
    rw [hpool, hsvs, goldilocks_get_anchor_eq_anchorAt] at hfc
    have hW' := walkEnd_of_fork_choice n hRoots C t _ _ (Finset.Subset.refl _) _ _ _ _ hfc
    have hsub : viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree ⊆ (fg_to_ac n.S).tree :=
      fun B hB => ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff _ _ B).1 hB).1
    have hR' := GoldilocksCorrectness.Proofs.Routines.rootsNameBlocksIn_mono hsub hRoots
    have hh : fi.head = head := by
      have e1 := (GoldilocksCorrectness.Proofs.Routines.ghost_eq_ok_iff_walkEnd hR').2 hW'
      have e2 := (GoldilocksCorrectness.Proofs.Routines.ghost_eq_ok_iff_walkEnd hR').2 hW
      exact Except.ok.inj (e1.symm.trans e2)
    -- the source and the head are blocks of the tree, whose stored chain states are computed
    have hsT : source ∈ n.S.T := by
      have h1 := GoldilocksCorrectness.Proofs.Routines.deepest?_mem hsrc
      have h2 := ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff _ _ _).1
        (Finset.mem_inter.1 h1).2).1
      exact ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree n.S source).1 h2).1
    have hhT : fi.head ∈ n.S.T :=
      (GoldilocksCorrectness.Proofs.Routines.ac_to_fg_head_mem C n'.A n.S t hInv.1.2.2.2.1
        hInv.1.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1 hInv.1.2.2.2.2.2.2.2.2.2.1.2.1.1 fi hfi).1
    rw [← hh] at hfrom
    have hb : (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).2 = some a := by
      rw [hInv.1.2.2.2.2.2.1 source hsT, hInv.1.2.2.2.2.2.1 fi.head hhT]
      exact (create_attestation_snd_eq_some_iff n _ _ _ _ _ _ a).2 hfrom
    exact GoldilocksCorrectness.Statements.Routines.lem49b_attestation_duty_runs C P X n n' t
      sent a fi source hRun hact ⟨τ, hτ, hle⟩ hfi hs hb
  tick_holds_sent := by
    intro _ C P X (n : NodeState V) t (n' : NodeState V) sent hRun hInv
    obtain ⟨hv, ha⟩ := (tick_holds_sent_rel C P X n t).of_outcome hRun
    refine ⟨fun vote h => ?_, fun a h => ?_⟩
    · rcases hv vote h with h' | h'
      · left
        show vote ∈ n'.A.pool vote.slot
        simp only [ACState.pool, List.mem_toFinset]
        exact h'
      · exact Or.inr h'
    · -- the attestation is well formed: the validator client built it at the chain-state height
      -- of a source in the node's tree (Lemma 49), which is at least `1` (Lemma 47 (a)), with the
      -- finality pair cut at that height
      obtain ⟨-, fi, source, hfi, hs, hbuilt, -⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem49_tick_attests C P X n n' t sent a hRun h
      obtain ⟨hsrc, -, -, -⟩ := ac_to_fg_eq_ok_facts hfi
      have hsT : source ∈ n.S.T := by
        have h1 : source ∈ n'.A.fast_blocks ∩ viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree :=
          GoldilocksCorrectness.Proofs.Routines.deepest?_mem (hsrc.symm.trans hs)
        have h2 := ((GoldilocksCorrectness.Proofs.Routines.mem_viable_tree_iff _ _ _).1
          (Finset.mem_inter.1 h1).2).1
        exact ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree n.S source).1 h2).1
      rw [hInv.1.2.2.2.2.2.1 source hsT] at hbuilt
      have hh := (GoldilocksCorrectness.Proofs.Routines.lem47_chain_state_heights C source
        source).1.1
      refine ha a h ?_
      rcases create_attestation_some_cases n.Λ n.v
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C source).h
          (GoldilocksCorrectness.Statements.Routines.chainStateOf C source).T_h.root (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root
          (n.S.σ fi.head).h_F with ⟨τ, -, -, he⟩ | ⟨he, -⟩
      · rw [he] at hbuilt
        cases Option.some.inj hbuilt
        simp only [attestation_well_formed, Id.run]
        cases hfp : finality_pair n.Λ (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root
            (n.S.σ fi.head).h_F with
        | none => exact decide_eq_true hh
        | some q =>
          by_cases hle : (GoldilocksCorrectness.Statements.Routines.chainStateOf C source).h ≤ q.hf
          · simp only [hle, if_true]
            exact decide_eq_true hh
          · simp only [hle, if_false, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
              Option.value, Option.get_some]
            exact Bool.and_eq_true_iff.2 ⟨decide_eq_true hh, decide_eq_true (lt_of_not_ge hle)⟩
      · rw [he] at hbuilt
        cases hbuilt
  attestation_sent_at_source := by
    intro n v h_c T_c h_j J h_F hLock hJ hTS hST hSTo
    obtain ⟨h1, h2⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem50_attestation_sent_at_source n.Λ v h_c T_c h_j
        J h_F hLock hJ hTS hST hSTo
    refine ⟨?_, fun hn ht hT => ?_⟩
    · rcases h1 with ⟨a, ha, hav⟩ | ⟨hnone, hb⟩
      · exact Or.inl ⟨a, (create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).1 ha, hav⟩
      · refine Or.inr ⟨fun a ha => ?_, hb⟩
        have := (create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).2 ha
        rw [hnone] at this
        cases this
    · obtain ⟨a, ha, hav⟩ := h2 hn ht hT
      exact ⟨a, (create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).1 ha, hav⟩
  attestation_carries_finality_pair := by
    intro n v h_c T_c h_j J h_F a ha hlt hj hT hTo hL
    exact GoldilocksCorrectness.Statements.Routines.lem92_attestation_carries_finality_pair n.Λ v
      h_c T_c h_j J h_F a ((create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).2 ha) hlt
      hj hT hTo hL

end GoldilocksCorrectness.Record
