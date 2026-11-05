module
public import GoldilocksCorrectness.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Score
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Statements.Routines.SupporterDefs
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-! The unnumbered
facts the proofs of Lemmas 13 to 15 (`Lemma13.lean`, `Lemma14.lean`, `Lemma15.lean`) and the
assemblies of phase 3 read about the node's tick (`tick`) and the wiring's dispatch of a delivered
object (`Goldilocks.Sts.receive`).

## The relation

- `KeepsConfirmation A A'`: `A'` has the lock entries, the saved confirmations, the fast blocks and
  the record of the confirmed tip of `A`.

## What is proved

- the receipts: `on_goldfish_vote_keepsConfirmation`, `ac_on_block_keepsConfirmation`,
  `on_block_keepsConfirmation`, `receive_keeps_confirmation`;
- the duties: `goldfish_vote_keepsConfirmation`, `propose_block_keepsConfirmation`, `attest_A`;
- the tick: `awake_since_record_awake` (the duty test from the stored `awakeSince`),
  `tick_ac_on_tick` (the tick's AC state keeps the four fields of the answer of its tick of the
  available chain), `tick_lock_entries_subset`;
- the readers: `fc_root_ancestorEq_get_anchor`, `mem_voter_block_tree_iff`,
  `ac_valid_payload_facts`, `tau_eq_some_blockStamp`;
- the transports along `KeepsVotes`: `pool_of_keepsVotes`, `tau_of_keepsVotes`,
  `voter_block_tree_of_keepsVotes`, `countedVotes_of_keepsVotes`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (on_block_eq on_attestation_frame record_awake_frame)
open GoldilocksCorrectness.Proofs.Routines (KeepsVotes on_goldfish_vote_cases_new
  revoke_locks_keepsVotes)
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREPost forIn_yield_inv)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The relation -/

section Relation

/-- `KeepsConfirmation A A'`: `A'` has the lock entries, the saved confirmations, the fast blocks
and the record of the confirmed tip of `A`.

The variables:
- `A`, `A'`: the two AC states.

Read aloud: `A'` holds what `A` holds of locks and confirmations. -/
def KeepsConfirmation (A A' : ACState V) : Prop :=
  A'.lock_entries = A.lock_entries ∧ A'.saved_confirmation = A.saved_confirmation ∧
    A'.fast_blocks = A.fast_blocks ∧ A'.latest_confirmed = A.latest_confirmed

omit [DecidableEq V] [Fintype V] in
/-- Every AC state keeps its own confirmation fields. -/
theorem KeepsConfirmation.refl (A : ACState V) : KeepsConfirmation A A :=
  ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `KeepsConfirmation` composes. -/
theorem KeepsConfirmation.trans {A A' A'' : ACState V} (h : KeepsConfirmation A A')
    (h' : KeepsConfirmation A' A'') : KeepsConfirmation A A'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

omit [DecidableEq V] [Fintype V] in
/-- Two AC states with the same confirmation fields keep each other's. -/
theorem KeepsConfirmation.symm {A A' : ACState V} (h : KeepsConfirmation A A') :
    KeepsConfirmation A' A :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

end Relation

/-! ## The receipts -/

section Receipts

omit [Fintype V] in
/-- The admission of a Goldfish vote keeps the confirmation fields: it writes the pool and the
vote stamps only.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `vote`: the vote. -/
theorem on_goldfish_vote_keepsConfirmation (C : Config) (P : Provisional V) (A : ACState V)
    (t : Time) (vote : GoldfishVote V) :
    KeepsConfirmation A (on_goldfish_vote C P A t vote) := by
  rcases on_goldfish_vote_cases_new C P A t vote with he | ⟨-, he⟩
  · rw [he]; exact KeepsConfirmation.refl A
  · rw [he]; exact ⟨rfl, rfl, rfl, rfl⟩

omit [Fintype V] in
/-- The admission of a block into the AC state keeps the confirmation fields: it writes the block
stamps, the pool and the vote stamps only.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `t`: the admission time;
  `B`: the block. -/
theorem ac_on_block_keepsConfirmation (C : Config) (P : Provisional V) (A : ACState V)
    (t : Time) (B : Block V) : KeepsConfirmation A (ac_on_block C P A t B) := by
  simp only [ac_on_block, Id.run]
  exact forIn_yield_inv B.votes _ (fun A' vote => on_goldfish_vote C P A' t vote)
    (fun A' => KeepsConfirmation A A') ⟨rfl, rfl, rfl, rfl⟩
    (fun A' vote _ hA' => hA'.trans (on_goldfish_vote_keepsConfirmation C P A' t vote))

variable [RootOrder]

/-- Receiving a block keeps the confirmation fields of the AC state: a refused block changes
nothing, an accepted one is admitted by `ac_on_block`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_keepsConfirmation (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) : KeepsConfirmation n.A (on_block C P X n B).A := by
  rw [on_block_eq]
  split
  · exact ac_on_block_keepsConfirmation C P n.A n.t B
  · exact KeepsConfirmation.refl n.A

/-- The wiring's dispatch of a delivered object keeps the lock entries, the saved confirmations,
the fast blocks and the record of the confirmed tip: a block is admitted by `ac_on_block`, a
Goldfish vote by `on_goldfish_vote`, and an attestation leaves the AC state unchanged.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object delivered.

Read aloud: a delivery changes none of the node's locks, saved confirmations, fast blocks or
confirmed tip. -/
theorem receive_keeps_confirmation (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (o : NamedObject V) :
    (Goldilocks.Sts.receive C P X n o).A.lock_entries = n.A.lock_entries ∧
      (Goldilocks.Sts.receive C P X n o).A.saved_confirmation = n.A.saved_confirmation ∧
      (Goldilocks.Sts.receive C P X n o).A.fast_blocks = n.A.fast_blocks ∧
      (Goldilocks.Sts.receive C P X n o).A.latest_confirmed = n.A.latest_confirmed := by
  cases o with
  | block B => exact on_block_keepsConfirmation C P X n B
  | gfVote vote => exact on_goldfish_vote_keepsConfirmation C P n.A n.t vote
  | attest a =>
      show KeepsConfirmation n.A (on_attestation n a).A
      rw [(on_attestation_frame n a).2.1]
      exact KeepsConfirmation.refl n.A

end Receipts

/-! ## The duties -/

section Duties

variable [RootOrder]

/-- Every answer of the Goldfish vote duty keeps the confirmation fields: it admits at most the
node's own vote.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the voter. -/
theorem goldfish_vote_keepsConfirmation (C : Config) (P : Provisional V) (A : ACState V)
    (Φ : Frame V) (t : Time) (v : V) :
    DREBPost (goldfish_vote C P A Φ t v) (KeepsConfirmation A) := by
  simp only [goldfish_vote]
  repeat' first
    | exact DREBPost.pure (KeepsConfirmation.refl A)
    | exact DREBPost.pure (on_goldfish_vote_keepsConfirmation C P A t _)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the proposal keeps the confirmation fields of the AC state: it ends by
receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_keepsConfirmation (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) :
    DREBPost (propose_block C P X n) (fun n' => KeepsConfirmation n.A n'.A) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_keepsConfirmation C P X n _)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the attestation duty has the AC state of the node state it starts from: it
writes the anti-slashing record and the FG state only.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_A (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => n'.A = n.A) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure rfl
    | exact DREBPost.pure (on_attestation_frame _ _).2.1
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

end Duties

/-! ## The tick -/

section Tick

omit [DecidableEq V] [Fintype V] in
/-- The duty test passes on the node state a tick's first step leaves, when the node's stored
`awakeSince` is `some τ` with `τ ≤ t₀`: `record_awake` keeps a present `awakeSince`.

The variables:
- `n`: the node state; `t`: the time of the tick; `t₀`: the time the test compares with;
- `τ`: the stored time.

Read aloud: a node awake since `τ ≤ t₀` passes the wake test for `t₀` at any tick. -/
theorem awake_since_record_awake {n : NodeState V} {t t₀ τ : Time}
    (hτ : n.awakeSince = some τ) (hle : τ ≤ t₀) : (record_awake n t).awake_since t₀ = true := by
  have hr : (record_awake n t).awakeSince = some τ := by
    simp only [record_awake, Id.run, hτ, reduceCtorEq, dite_false]
    exact hτ
  simp only [NodeState.awake_since, Id.run, hr, ne_eq, reduceCtorEq, not_false_eq_true,
    dite_true, Option.value, Option.get_some]
  exact decide_eq_true hle

variable [RootOrder]

/-- What a tick leaves of the AC state is what its tick of the available chain answered, in the
lock entries, the saved confirmations, the fast blocks and the record of the confirmed tip. The
tick of the available chain runs on the node's AC state over the frame of its FG state, for its
validator, with both wake tests the duty test `(record_awake n t).awake_since (duty_window_start C
(C.slot t))`; the proposal and the attestation duty, when they run, keep the four fields.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: an `.ok` outcome of the tick, the node state and the objects sent;
- `A₁`: the answer of the tick of the available chain; `out`, `out'`: the objects sent before and
  after it ran.

Read aloud: the tick's locks and confirmations are those its tick of the available chain left. -/
theorem tick_ac_on_tick (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V)
    (t : Time) (sent : List (NamedObject V))
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes) :
    ∃ (A₁ : ACState V) (out out' : List (NamedObject V)),
      (ac_on_tick C P n.A (fg_to_ac n.S) t n.v
          ((record_awake n t).awake_since (duty_window_start C (C.slot t)))
          ((record_awake n t).awake_since (duty_window_start C (C.slot t)))).run out =
        .ok (A₁, out') ∧ KeepsConfirmation A₁ n'.A := by
  obtain ⟨hS, hA, hv, -⟩ := record_awake_frame n t
  have h : DREBPost (tick C P X n t) (fun n' => ∃ (A₁ : ACState V)
      (out out' : List (NamedObject V)),
      (ac_on_tick C P n.A (fg_to_ac n.S) t n.v
          ((record_awake n t).awake_since (duty_window_start C (C.slot t)))
          ((record_awake n t).awake_since (duty_window_start C (C.slot t)))).run out =
        .ok (A₁, out') ∧ KeepsConfirmation A₁ n'.A) := by
    simp only [tick]
    refine DREBPost.bind (P := fun A₁ => ∃ (out out' : List (NamedObject V)),
      (ac_on_tick C P n.A (fg_to_ac n.S) t n.v
          ((record_awake n t).awake_since (duty_window_start C (C.slot t)))
          ((record_awake n t).awake_since (duty_window_start C (C.slot t)))).run out =
        .ok (A₁, out')) (fun out A₁ out' h => ⟨out, out', by rw [← hS, ← hA, ← hv]; exact h⟩)
      (fun A₁ hA₁ => ?_)
    obtain ⟨out, out', hrun⟩ := hA₁
    have hk : ∀ n₁ : NodeState V, KeepsConfirmation A₁ n₁.A →
        ∃ (A₂ : ACState V) (out out' : List (NamedObject V)),
          (ac_on_tick C P n.A (fg_to_ac n.S) t n.v
              ((record_awake n t).awake_since (duty_window_start C (C.slot t)))
              ((record_awake n t).awake_since (duty_window_start C (C.slot t)))).run out =
            .ok (A₂, out') ∧ KeepsConfirmation A₂ n₁.A :=
      fun n₁ h₁ => ⟨A₁, out, out', hrun, h₁⟩
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBPost.bind (propose_block_keepsConfirmation C P X _) (fun n₄ h₄ => ?_)
      refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
      · refine DREBPost.bind (attest_A C n₄) ?_
        intro n₅ h₅
        refine DREBPost.pure (hk n₅ ?_)
        rw [h₅]
        exact h₄
      · exact DREBPost.pure (hk n₄ h₄)
    · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
      · refine DREBPost.bind (attest_A C _) ?_
        intro n₅ h₅
        refine DREBPost.pure (hk n₅ ?_)
        rw [h₅]
        exact KeepsConfirmation.refl A₁
      · exact DREBPost.pure (hk _ (KeepsConfirmation.refl A₁))
  exact DREBPost.of_outcome h hRun

/-- Away from the vote time and the support cutoff of its slot, the tick of the available chain
only deletes lock entries: neither `if` of `ac_on_tick` is taken, and its answer is
`expireLocks A t`.

The variables:
- `C`, `P`: the parameters and the values; `A`: the AC state; `Φ`: the frame; `t`: the time;
  `v`: the node's validator; `b`, `b'`: the two wake tests. -/
theorem ac_on_tick_lock_entries_subset (C : Config) (P : Provisional V) (A : ACState V)
    (Φ : Frame V) (t : Time) (v : V) (b b' : Bool)
    (hNotVote : t ≠ C.t_ (C.slot t) + C.Δ) (hNotCutoff : t ≠ C.t_ (C.slot t) + 2 * C.Δ) :
    DREBPost (ac_on_tick C P A Φ t v b b') (fun A₁ => A₁.lock_entries ⊆ A.lock_entries) := by
  simp only [ac_on_tick]
  refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact absurd hc.1 hNotVote
  · refine DREBPost.ite (fun hc => ?_) (fun _ => ?_)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact absurd hc.1 hNotCutoff
    · exact DREBPost.pure (Finset.filter_subset _ _)

/-- Away from the vote time and the support cutoff of its slot, a tick keeps a subset of the
node's lock entries: it deletes those past their deadline and runs neither the revocation nor
the confirmation update.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: an `.ok` outcome of the tick, the node state and the objects sent.

Read aloud: a tick at neither duty time of its slot adds no lock entry. -/
theorem tick_lock_entries_subset (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V))
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hNotVote : t ≠ C.t_ (C.slot t) + C.Δ) (hNotCutoff : t ≠ C.t_ (C.slot t) + 2 * C.Δ) :
    n'.A.lock_entries ⊆ n.A.lock_entries := by
  obtain ⟨A₁, out, out', hrun, hk⟩ := tick_ac_on_tick C P X n n' t sent hRun
  rw [hk.1]
  exact ac_on_tick_lock_entries_subset C P n.A _ t _ _ _ hNotVote hNotCutoff out A₁ out' hrun

end Tick

/-! ## The readers -/

section Readers

variable [RootOrder]

omit [Fintype V] in
/-- The anchor of every walk is `Φ.fc_root` or a descendant of it: it is `Φ.fc_root`, or a block
of the viable tree, every block of which is `Φ.fc_root` or a descendant of it.

The variables:
- `A`: the AC state; `Φ`: the frame; `t`: the time the anchor is read at.

Read aloud: `Φ.fc_root` is the anchor or an ancestor of it. -/
theorem fc_root_ancestorEq_get_anchor (A : ACState V) (Φ : Frame V) (t : Time) :
    Φ.fc_root.AncestorEq (get_anchor A Φ t) := by
  simp only [get_anchor, Id.run]
  generalize hD : Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B} = D
  cases D with
  | none => exact ancestorEq_refl Φ.fc_root
  | some B =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
    have hmem := deepest?_mem hD
    simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true] at hmem
    exact hmem.1.2.1

omit [Fintype V] [RootOrder] in
/-- A block is in the voter's tree of slot `s'` exactly when it is a block of `Φ.tree` with a
stamp in `A`, and the stamp is strictly before the view freeze of slot `s' − 1`, or the block is a
slot-`s'` block of `Φ.tree` or an ancestor of one.

The variables:
- `C`: the configuration; `A`: the AC state; `Φ`: the frame; `s'`: the slot of the vote;
- `vbt`: the voter's tree; `B`: the block.

Read aloud: the voter's tree holds the stamped blocks of the frame's tree that are early or lead
to a slot-`s'` block. -/
theorem mem_voter_block_tree_iff (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot)
    (vbt : Finset (Block V)) (h : voter_block_tree C A Φ s' = .ok vbt) (B : Block V) :
    B ∈ vbt ↔ B ∈ Φ.tree ∧ ∃ τ : Stamp, A.timestamp_block B = some τ ∧
      (τ < ((C.t_ (s' - 1) + 3 * C.Δ : Time) : Stamp) ∨
        ∃ B' ∈ Φ.tree, B'.slot = s' ∧ B.AncestorEq B') := by
  simp only [voter_block_tree] at h
  rw [mem_of_filterM_eq_ok_iff _ _ _ h]
  refine and_congr_right fun _ => ?_
  cases hb : A.timestamp_block B with
  | none => simp [liftM_none, bind, Except.bind]
  | some τ =>
    simp only [liftM_some, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Bool.or_eq_true, decide_eq_true_eq, Option.some.injEq, Finset.mem_filter]
    constructor
    · rintro (h1 | ⟨B', ⟨hB', hs⟩, hanc⟩)
      · exact ⟨τ, rfl, Or.inl h1⟩
      · exact ⟨τ, rfl, Or.inr ⟨B', hB', hs, hanc⟩⟩
    · rintro ⟨τ', rfl, h1 | ⟨B', hB', hs, hanc⟩⟩
      · exact Or.inl h1
      · exact Or.inr ⟨B', ⟨hB', hs⟩, hanc⟩

omit [Fintype V] [RootOrder] in
/-- What a valid payload says of a block's votes: every Goldfish vote of `B.votes` has the slot
`B.slot − 1` and a validator of the committee of that slot, and every vote of `B.support_votes` is
one of `B.votes`.

The variables:
- `P`: the values, with the committees; `B`: the block.

Read aloud: a valid payload holds votes of the previous slot's committee, for that slot. -/
theorem ac_valid_payload_facts (P : Provisional V) (B : Block V)
    (h : ac_valid_payload P B = true) :
    (∀ vote ∈ B.votes, vote.slot = B.slot - 1) ∧ (∀ vote ∈ B.support_votes, vote ∈ B.votes) ∧
      ∀ vote ∈ B.votes, vote.val_index ∈ P.committee (B.slot - 1) := by
  simp only [ac_valid_payload, decide_eq_true_eq] at h
  exact h

omit [Fintype V] [RootOrder] in
/-- A vote that resolves at `y` in `A`, whose head is the root of the block `H` of `Φ.tree`, has
`H` stamped in `A` at `y` or earlier, when the roots of `Φ.tree` name its blocks: the resolution
time is the later of the vote's stamp and its head block's stamp.

The variables:
- `A`: the AC state; `Φ`: the frame; `vote`: the vote; `H`: the head block; `y`: the resolution
  time.

Read aloud: a vote resolves no earlier than its head block was stamped. -/
theorem tau_eq_some_blockStamp {A : ACState V} {Φ : Frame V} {vote : GoldfishVote V}
    {H : Block V} {y : Stamp} (hRoots : RootsNameBlocksIn Φ.tree) (hH : H ∈ Φ.tree)
    (hroot : H.root = vote.head) (h : A.tau Φ vote = .ok (some y)) :
    ∃ τ : Stamp, A.timestamp_block H = some τ ∧ τ ≤ y := by
  simp only [ACState.tau, resolution_time] at h
  obtain ⟨H?, hH?, h1⟩ := dre_bind_eq_ok h
  rw [blockWithRoot_eq_ok hRoots, find?_eq_some hRoots hH hroot] at hH?
  cases hH?
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
    Option.get_some] at h1
  split at h1
  · cases hv : A.timestamp_vote vote with
    | none => simp [hv, liftM_none, bind, Except.bind] at h1
    | some τ =>
      cases hb : A.timestamp_block H with
      | none => simp [hv, hb, liftM_some, liftM_none, bind, Except.bind] at h1
      | some τH =>
        simp only [hv, hb, liftM_some, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          Option.some.injEq] at h1
        exact ⟨τH, rfl, h1 ▸ le_max_right τ τH⟩
  · cases h1

end Readers

/-! ## The transports along `KeepsVotes` -/

section Transports

omit [Fintype V] in
/-- An AC state with the pool of `A` has `A`'s pool of every slot. -/
theorem pool_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (s : Slot) :
    A'.pool s = A.pool s := by
  unfold ACState.pool
  rw [h.1]

omit [Fintype V] in
/-- An AC state with the vote and block stamps of `A` has `A`'s resolution times. -/
theorem tau_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (Φ : Frame V)
    (vote : GoldfishVote V) : A'.tau Φ vote = A.tau Φ vote := by
  unfold ACState.tau
  rw [h.2.1, h.2.2]

omit [Fintype V] in
/-- An AC state with the block stamps of `A` has `A`'s voter trees. -/
theorem voter_block_tree_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (C : Config)
    (Φ : Frame V) (s' : Slot) : voter_block_tree C A' Φ s' = voter_block_tree C A Φ s' := by
  unfold voter_block_tree
  rw [h.2.2]

omit [Fintype V] in
/-- The sets a Goldfish vote counts read only the pool, the vote stamps and the resolution times,
so an AC state that keeps `A`'s counts the same sets. -/
theorem countedVotes_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (C : Config)
    (Φ : Frame V) (s' : Slot) (votes support_votes : Finset (GoldfishVote V)) :
    CountedVotes C A' Φ s' votes support_votes ↔ CountedVotes C A Φ s' votes support_votes := by
  unfold CountedVotes
  simp only [pool_of_keepsVotes h, tau_of_keepsVotes h, h.2.1]

omit [DecidableEq V] [Fintype V] in
/-- Deleting lock entries keeps the pool and the stamps. -/
theorem expireLocks_keepsVotes (A : ACState V) (t : Time) : KeepsVotes A (expireLocks A t) :=
  ⟨rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- Deleting lock entries keeps the saved confirmations, the fast blocks and the record of the
confirmed tip. -/
theorem expireLocks_confirmation (A : ACState V) (t : Time) :
    (expireLocks A t).saved_confirmation = A.saved_confirmation ∧
      (expireLocks A t).fast_blocks = A.fast_blocks ∧
      (expireLocks A t).latest_confirmed = A.latest_confirmed :=
  ⟨rfl, rfl, rfl⟩

omit [Fintype V] in
/-- **The early supporters of a block in an AC state with `A`'s pool and stamps.**
`EarlySupporterOf` reads only the pool, the vote stamps and the resolution times, so an AC state
`A'` with the pool and the stamps of `A` (`KeepsVotes A A'`) has the early supporters of `A`.

The variables:
- `A`, `A'`: the two AC states; `h`: `A'` has the pool and the stamps of `A`; `C`: the
  parameters; `Φ`: the frame; `s`: the slot; `B`: the block; `u`: the validator.

Read aloud: deleting lock entries, or any change that keeps the votes and the stamps, keeps who
supports `B` early. -/
theorem earlySupporterOf_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (C : Config)
    (Φ : Frame V) (s : Slot) (B : Block V) (u : V) :
    EarlySupporterOf C A' Φ s B u ↔ EarlySupporterOf C A Φ s B u := by
  unfold EarlySupporterOf ACState.pool ACState.tau
  rw [h.1, h.2.1, h.2.2]

omit [Fintype V] in
/-- **A single vote in the pool, in an AC state with `A`'s pool and stamps.**
`VotesOnceInPoolFor` reads only the pool and the resolution times, so an AC state `A'` with the
pool and the stamps of `A` (`KeepsVotes A A'`) answers it as `A` does.

The variables:
- `A`, `A'`: the two AC states; `h`: `A'` has the pool and the stamps of `A`; `Φ`: the frame;
  `s`: the slot; `R`: the block; `v`: the validator.

Read aloud: deleting lock entries, or any change that keeps the votes and the stamps, keeps that
`v` voted once, for `R`'s chain, in the pool. -/
theorem votesOnceInPoolFor_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (Φ : Frame V)
    (s : Slot) (R : Block V) (v : V) :
    VotesOnceInPoolFor A' Φ s R v ↔ VotesOnceInPoolFor A Φ s R v := by
  unfold VotesOnceInPoolFor ACState.pool ACState.tau
  rw [h.1, h.2.1, h.2.2]

omit [Fintype V] in
/-- **A single early vote in the pool, in an AC state with `A`'s pool and stamps.**
`EarlyVoteOnceFor` reads only the pool and the resolution times, so an AC state `A'` with the pool
and the stamps of `A` (`KeepsVotes A A'`) answers it as `A` does.

The variables:
- `A`, `A'`: the two AC states; `h`: `A'` has the pool and the stamps of `A`; `C`: the
  parameters; `Φ`: the frame; `s`: the slot; `B`: the block; `v`: the validator.

Read aloud: deleting lock entries, or any change that keeps the votes and the stamps, keeps that
`v` has one slot-`s` vote in the pool, for `B`'s root, resolved early.

Added by the record migration, step 1h, for the execution proofs that read the pool
after `expireLocks` through the bodies of `ACState.pool` and `ACState.tau`. -/
theorem earlyVoteOnceFor_of_keepsVotes {A A' : ACState V} (h : KeepsVotes A A') (C : Config)
    (Φ : Frame V) (s : Slot) (B : Block V) (v : V) :
    EarlyVoteOnceFor C A' Φ s B v ↔ EarlyVoteOnceFor C A Φ s B v := by
  unfold EarlyVoteOnceFor ACState.pool ACState.tau
  rw [h.1, h.2.1, h.2.2]

end Transports

end GoldilocksCorrectness.Proofs.Routines
