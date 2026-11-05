module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Locks
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.ChainConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
import all Goldilocks.AC.State

@[expose] public section

/-!
# The statements about the confirmation update and the locks, over a model

The audited statements of `GoldilocksCorrectness/Statements/Routines/AttestationStatements.lean`
(`fast_blocks_ancestorEq_saved`), `ChainConfirmationStatements.lean` (Lemma 77,
`saved_confirmation_F_ancestorEq`), `ConfirmationStatements.lean` (Lemmas 25, 28, 30, 35, 36, 37,
`revoke_locks_keeps_entry`) and `LockStatements.lean` (Lemmas 5, 38), over a model `M` whose facts
`F` hold: each takes the record's predicate `ConfirmationUpdated M C P n t s n'` or
`LocksRevoked M P n t s n'` where the landed statement takes the spec's answer, its other
hypotheses read on `n`, its conclusion on `n'`. A lock entry the landed statement names as
`LockEntry.mk B d` is an entry with the block `B` and the deadline `d`; the lock entries of the
update's input are, on `n`, those whose deadline is after `t`.

The recovery section states each landed statement again, as the landed statement (`type_of%`), at
the AC state `n.A` and the frame `fg_to_ac n.S` of a node state `n`, and proves it from its record
form at the spec's model, through the bridges `confirmationUpdated_at_node` and
`locksRevoked_at_node`, with the hypotheses those bridges read and the landed statement does not
have: that no two blocks of the frame's tree share a root, and, for the confirmation update, that
every lock entry of `n` has a deadline after `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_compatible compatible_iff
  conflicts_iff conflicts_comm conflicts_of_ancestorEq_conflicts occurrenceBefore_eq_true_iff
  mem_participants_iff voters_count_eq supportersOf mem_supportersOf_iff goldfish_score_eq_ok
  dre_bind_ok equivocators_support_eq_empty supportersOf_support_subset_participants)
open GoldilocksCorrectness.Record.Proofs.Routines (confirmationUpdated_walk voters_count_eq_spec
  mem_earlyVotes mem_lateVotes earlyVotes_subset_lateVotes lateVotes_subset
  confirmationUpdated_saved_some confirmationUpdated_entries_keep
  confirmationUpdated_entries_cases)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The confirmation update -/

/-- When the update of slot `s ≠ 0` saves `C'`, every fast block is `C'` or an ancestor of `C'`
(the record form of the statement `fast_blocks_ancestorEq_saved`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `C'`: the saved confirmation.

Read aloud: every fast block leads to the saved confirmation. -/
theorem fast_blocks_ancestorEq_saved [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {C' : Block V}
    -- the slot of the update is not `0`
    (hs : s ≠ 0)
    -- the confirmation update of slot `s` leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n')
    -- `n'` saves the confirmation `C'` for the slot `s − 1`
    (hSaved : n'.savedConfirmation (s - 1) = some C') :
    ∀ L ∈ n'.fastBlocks, L.AncestorEq C' :=
  GoldilocksCorrectness.Record.Proofs.Routines.fast_blocks_ancestorEq_saved hs hUpdate hSaved

/-- **Lemma 77 over the record**, the statement form of
`GoldilocksCorrectness.Record.Proofs.Routines.lem77_update_confirmation_extends_voter_majority_chain`.

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the supporters.

Read aloud: the saved confirmation extends a voter majority's chain. -/
theorem lem77_update_confirmation_extends_voter_majority_chain [RootOrder]
    {M : GoldilocksModel V} (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N}
    {t : Time} {s : Slot} (B : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the frame's tree share a root
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    -- the frame's finalized block is `B` or an ancestor of `B`
    (hF : (M.fg_to_ac n).F.AncestorEq B)
    -- every block from the frame's finalized block to `B` is in the frame's tree
    (hPathF : ∀ P' : Block V, (M.fg_to_ac n).F.AncestorEq P' → P'.AncestorEq B →
      P' ∈ (M.fg_to_ac n).tree)
    -- each member of `Hs` is an early supporter of `B`
    (hHs : ∀ v ∈ Hs, EarlySupporterOf M C n (s - 1) B v)
    -- every vote of the slot has the slot `s − 1`
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    -- the voters are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    -- the update leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∀ C' : Block V, n'.savedConfirmation (s - 1) = some C' → B.AncestorEq C' :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem77_update_confirmation_extends_voter_majority_chain
    F B Hs hs hRoots hF hPathF hHs hSlot hVoters hUpdate

/-- When the update of slot `s ≥ 1` saves `C'`, the frame's finalized block is `C'` or an ancestor
of `C'` (the record form of the statement `saved_confirmation_F_ancestorEq`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: the saved confirmation descends from the finalized block. -/
theorem saved_confirmation_F_ancestorEq [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the confirmation update of slot `s` leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    ∀ C' : Block V, n'.savedConfirmation (s - 1) = some C' → (M.fg_to_ac n).F.AncestorEq C' :=
  GoldilocksCorrectness.Record.Proofs.Routines.saved_confirmation_F_ancestorEq hs hUpdate

/-- **Lemma 25 over the record.** The update of slot `s ≥ 1` saves `B` and advances the record of
the confirmed tip with `B`, under the hypotheses of `update_confirmation_of_voter_majority` (the
record form of `lem25_update_confirmation_confirms_voter_majority_block`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the voters.

Read aloud: an early unanimous majority makes the update confirm its block. -/
theorem lem25_update_confirmation_confirms_voter_majority_block [RootOrder]
    {M : GoldilocksModel V} (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N}
    {t : Time} {s : Slot} (B : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the frame's tree share a root
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    -- `B` is not the genesis block
    (hBne : B ≠ Block.genesis)
    -- the frame's finalized block is `B` or an ancestor of `B`
    (hF : (M.fg_to_ac n).F.AncestorEq B)
    -- every block from the frame's finalized block to `B` is in the frame's tree
    (hPathF : ∀ P' : Block V, (M.fg_to_ac n).F.AncestorEq P' → P'.AncestorEq B →
      P' ∈ (M.fg_to_ac n).tree)
    -- each member of `Hs` has exactly one slot-`(s − 1)` vote, early, with head `B`
    (hHs : ∀ v ∈ Hs, EarlyVoteOnceFor M C n (s - 1) B v)
    -- every vote of the slot has the slot `s − 1`
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    -- the voters are fewer than twice `Hs`
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    -- the block of every lock entry of `n` live at `t` is compatible with `B`
    (hNoVeto : ∀ e ∈ n.lockEntries, M.is_live n t e = true → e.B.compatible B = true)
    -- the update leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    n'.savedConfirmation (s - 1) = some B ∧
      n'.latestConfirmed = M.advance (M.fg_to_ac n) n.latestConfirmed (some B) :=
  let h := GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_of_voter_majority F B
    Hs hs hRoots hBne hF hPathF hHs hSlot hVoters hNoVeto hUpdate
  ⟨h.1, h.2.1⟩

/-- **Lemma 28 over the record.** Under the hypotheses of Lemma 25 and a committee of slot `s − 1`
at most twice `Hs`, `B` is a fast block of `n'` and `n'` holds a lock entry on `B` with the deadline
`C.t_ (s − 1 + C.k) + 5 · C.Δ` (the record form of
`lem28_update_confirmation_fast_locks_voter_majority_block`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the block; `Hs`: the voters.

Read aloud: with half the committee, the confirmed block is fast and locked. -/
theorem lem28_update_confirmation_fast_locks_voter_majority_block [RootOrder]
    {M : GoldilocksModel V} (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N}
    {t : Time} {s : Slot} (B : Block V) (Hs : Finset V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hBne : B ≠ Block.genesis)
    (hF : (M.fg_to_ac n).F.AncestorEq B)
    (hPathF : ∀ P' : Block V, (M.fg_to_ac n).F.AncestorEq P' → P'.AncestorEq B →
      P' ∈ (M.fg_to_ac n).tree)
    (hHs : ∀ v ∈ Hs, EarlyVoteOnceFor M C n (s - 1) B v)
    (hSlot : ∀ vote ∈ M.votesHeldSet n (s - 1), vote.slot = s - 1)
    (hVoters : M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Hs.card)
    -- the slot-`(s − 1)` committee is at most twice `Hs`
    (hHalf : (P.committee (s - 1)).card ≤ 2 * Hs.card)
    (hNoVeto : ∀ e ∈ n.lockEntries, M.is_live n t e = true → e.B.compatible B = true)
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    B ∈ n'.fastBlocks ∧ ∃ e ∈ n'.lockEntries, e.B = B ∧ e.d = C.t_ (s - 1 + C.k) + 5 * C.Δ :=
  (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_of_voter_majority F B Hs hs
    hRoots hBne hF hPathF hHs hSlot hVoters hNoVeto hUpdate).2.2 hHalf

/-- The count a saved confirmation passed: when the update of slot `s ≥ 1` saves `B`, the late
voters are fewer than twice the equivocators of the support votes plus the supporters of `B`.

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `B`: the saved confirmation.

Read aloud: a saved confirmation passed the update's count. -/
theorem confirmationUpdated_saved_count [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} {B : Block V}
    (hs : 1 ≤ s) (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hUpdate : ConfirmationUpdated M C P n t s n')
    (hSaved : n'.savedConfirmation (s - 1) = some B) :
    voters_count (LateVotes M C n (s - 1)) <
      2 * ((equivocators {vote ∈ EarlyVotes M C n (s - 1) |
          no_second_vote_in (LateVotes M C n (s - 1)) vote = true}).card +
        (supportersOf (M.fg_to_ac n)
          {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
          {vote ∈ EarlyVotes M C n (s - 1) | no_second_vote_in (LateVotes M C n (s - 1)) vote = true}
          (s - 1) B).card) := by
  obtain ⟨H, b, -, hb, hS⟩ := confirmationUpdated_walk F hs hRoots hUpdate
  rw [hSaved] at hS
  cases b with
  | false => simp at hS
  | true =>
  simp only [if_true, Option.some.injEq] at hS
  subst hS
  simp only [goldfish_score_eq_ok hRoots, dre_bind_ok, pure, Except.pure, Except.ok.injEq,
    decide_eq_true_eq] at hb
  exact hb

/-- A supporter of `B` at the first node has a late vote at the second node, when every early vote
of the first node is held by the second node or the second node holds two votes of its validator,
and every vote of the second node is late there.

The variables:
- `M`: the model; `C`: the configuration; `n₁`, `n₂`: the two node states; `s'`: the slot;
  `B`: the block; `late₂`: the late votes of the second node.

Read aloud: the first node's supporters are voters at the second. -/
theorem supportersOf_subset_participants_of_reach {M : GoldilocksModel V} {C : Config}
    {n₁ n₂ : M.N} {s' : Slot} (B : Block V) (late₂ : Finset (GoldfishVote V))
    (hPoolLate₂ : M.votesHeldSet n₂ s' ⊆ late₂)
    (hReach₁₂ : ∀ vote ∈ M.votesHeldSet n₁ s',
      (∃ y : Stamp, ResolvesAt M n₁ vote y ∧ occurrenceBefore (some y) (C.t_ s' + 2 * C.Δ) = true) →
      vote ∈ M.votesHeldSet n₂ s' ∨
        ∃ u₁ ∈ M.votesHeldSet n₂ s', ∃ u₂ ∈ M.votesHeldSet n₂ s',
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index) :
    supportersOf (M.fg_to_ac n₁)
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true}
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true} s' B ⊆
      participants late₂ := by
  intro v hv
  obtain ⟨x, hx, hxv, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv
  obtain ⟨hxp, y, hτ, hy⟩ := mem_earlyVotes.1 (Finset.mem_filter.1 hx).1
  rcases hReach₁₂ x hxp ⟨y, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨y, rfl, hy⟩⟩ with
    h | ⟨u₁, hu₁, -, -, -, hval, -⟩
  · exact (mem_participants_iff _ _).2 ⟨x, hPoolLate₂ h, hxv⟩
  · exact (mem_participants_iff _ _).2 ⟨u₁, hPoolLate₂ hu₁, hval.trans hxv⟩

/-- A validator that supports `B₁` at the first node and `B₂` at the second makes `B₁` and `B₂`
compatible, under the reach hypothesis of `supportersOf_subset_participants_of_reach`, when every
vote of the second node is late there and no two blocks of the two frame trees share a root.

The variables:
- `M`: the model; `C`: the configuration; `n₁`, `n₂`: the two node states; `s'`: the slot;
  `B₁`, `B₂`: the blocks; `v`: the validator.

Read aloud: a common supporter makes the two blocks compatible. -/
theorem compatible_of_common_supporter {M : GoldilocksModel V} {C : Config} {n₁ n₂ : M.N}
    {s' : Slot} (B₁ B₂ : Block V) (v : V)
    (hRoots : RootsNameBlocksIn ((M.fg_to_ac n₁).tree ∪ (M.fg_to_ac n₂).tree))
    (hPoolLate₂ : M.votesHeldSet n₂ s' ⊆ LateVotes M C n₂ s')
    (hReach₁₂ : ∀ vote ∈ M.votesHeldSet n₁ s',
      (∃ y : Stamp, ResolvesAt M n₁ vote y ∧ occurrenceBefore (some y) (C.t_ s' + 2 * C.Δ) = true) →
      vote ∈ M.votesHeldSet n₂ s' ∨
        ∃ u₁ ∈ M.votesHeldSet n₂ s', ∃ u₂ ∈ M.votesHeldSet n₂ s',
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    (hv₁ : v ∈ supportersOf (M.fg_to_ac n₁)
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true}
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true} s' B₁)
    (hv₂ : v ∈ supportersOf (M.fg_to_ac n₂)
      {vote ∈ EarlyVotes M C n₂ s' | no_second_vote_in (LateVotes M C n₂ s') vote = true}
      {vote ∈ EarlyVotes M C n₂ s' | no_second_vote_in (LateVotes M C n₂ s') vote = true} s' B₂) :
    B₁.compatible B₂ = true := by
  obtain ⟨x, hx, hxv, -, -, H₁, hH₁, hr₁, hB₁⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv₁
  obtain ⟨y, hy, hyv, -, -, H₂, hH₂, hr₂, hB₂⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv₂
  obtain ⟨hxp, τ, hτ, hτc⟩ := mem_earlyVotes.1 (Finset.mem_filter.1 hx).1
  have hN := (Finset.mem_filter.1 hy).2
  simp only [no_second_vote_in, decide_eq_true_eq] at hN
  have hxy : x = y := by
    rcases hReach₁₂ x hxp ⟨τ, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨τ, rfl, hτc⟩⟩ with
      h | ⟨u₁, hu₁, u₂, hu₂, hne, hval₁, hval₂⟩
    · rcases hN x (hPoolLate₂ h) with h' | h'
      · exact h'
      · exact absurd (hxv.trans hyv.symm) h'
    · have e₁ : u₁ = y := (hN u₁ (hPoolLate₂ hu₁)).resolve_right
        (fun h' => h' (hval₁.trans (hxv.trans hyv.symm)))
      have e₂ : u₂ = y := (hN u₂ (hPoolLate₂ hu₂)).resolve_right
        (fun h' => h' (hval₂.trans (hxv.trans hyv.symm)))
      exact absurd (e₁.trans e₂.symm) hne
  subst hxy
  have hH : H₁ = H₂ := hRoots H₁ (Finset.mem_union_left _ hH₁) H₂ (Finset.mem_union_right _ hH₂)
    (hr₁.trans hr₂.symm)
  subst hH
  exact (compatible_iff _ _).2 (ancestorEq_compatible hB₁ hB₂)

/-- **Lemma 30 over the record.** Two confirmation updates of slot `s ≥ 1` from the node states
`n₁` and `n₂`, saving `C₁` and `C₂`, save compatible blocks, when no two blocks of the two frame
trees share a root, every vote of either node's slot is stamped strictly before
`C.t_ (s − 1) + 6 · C.Δ`, and every vote of either node resolving strictly before
`C.t_ (s − 1) + 2 · C.Δ` is held by the other node, or the other holds two votes of its validator
(the record form of `lem30_saved_confirmations_compatible`).

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n₁`, `n₁'`, `n₂`, `n₂'`: the node
  states before and after the two updates; `t₁`, `t₂`: their times; `s`: the slot;
  `C₁`, `C₂`: the saved confirmations.

Read aloud: two updates of one slot over reachable votes save blocks of one chain. -/
theorem lem30_saved_confirmations_compatible [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n₁ n₁' n₂ n₂' : M.N} {t₁ t₂ : Time} {s : Slot}
    (C₁ C₂ : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the two frame trees share a root
    (hRoots : RootsNameBlocksIn ((M.fg_to_ac n₁).tree ∪ (M.fg_to_ac n₂).tree))
    -- every vote of `n₁`'s slot is stamped strictly before the late cutoff
    (hLate₁ : ∀ vote ∈ M.votesHeldSet n₁ (s - 1), ∃ τ : Stamp, n₁.voteStamp vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- every vote of `n₂`'s slot is stamped strictly before the late cutoff
    (hLate₂ : ∀ vote ∈ M.votesHeldSet n₂ (s - 1), ∃ τ : Stamp, n₂.voteStamp vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    -- every early vote of `n₁` is held by `n₂`, or `n₂` holds two votes of its validator
    (hReach₁₂ : ∀ vote ∈ M.votesHeldSet n₁ (s - 1),
      (∃ y : Stamp, ResolvesAt M n₁ vote y ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ M.votesHeldSet n₂ (s - 1) ∨
        ∃ u₁ ∈ M.votesHeldSet n₂ (s - 1), ∃ u₂ ∈ M.votesHeldSet n₂ (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- every early vote of `n₂` is held by `n₁`, or `n₁` holds two votes of its validator
    (hReach₂₁ : ∀ vote ∈ M.votesHeldSet n₂ (s - 1),
      (∃ y : Stamp, ResolvesAt M n₂ vote y ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ M.votesHeldSet n₁ (s - 1) ∨
        ∃ u₁ ∈ M.votesHeldSet n₁ (s - 1), ∃ u₂ ∈ M.votesHeldSet n₁ (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- the update from `n₁` leaves `n₁'` and saves `C₁`
    (hUpdate₁ : ConfirmationUpdated M C P n₁ t₁ s n₁')
    (hSaved₁ : n₁'.savedConfirmation (s - 1) = some C₁)
    -- the update from `n₂` leaves `n₂'` and saves `C₂`
    (hUpdate₂ : ConfirmationUpdated M C P n₂ t₂ s n₂')
    (hSaved₂ : n₂'.savedConfirmation (s - 1) = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hRoots₁ : RootsNameBlocksIn (M.fg_to_ac n₁).tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_left _ hB) B' (Finset.mem_union_left _ hB') h
  have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac n₂).tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_right _ hB) B' (Finset.mem_union_right _ hB') h
  have hel₁ := confirmationUpdated_saved_count F hs hRoots₁ hUpdate₁ hSaved₁
  have hel₂ := confirmationUpdated_saved_count F hs hRoots₂ hUpdate₂ hSaved₂
  rw [equivocators_support_eq_empty _ _ earlyVotes_subset_lateVotes, Finset.card_empty,
    zero_add] at hel₁ hel₂
  have hPL₁ : M.votesHeldSet n₁ (s - 1) ⊆ LateVotes M C n₁ (s - 1) :=
    fun vote hv => mem_lateVotes.2 ⟨hv, hLate₁ vote hv⟩
  have hPL₂ : M.votesHeldSet n₂ (s - 1) ⊆ LateVotes M C n₂ (s - 1) :=
    fun vote hv => mem_lateVotes.2 ⟨hv, hLate₂ vote hv⟩
  have hSL₁ : {vote ∈ EarlyVotes M C n₁ (s - 1) |
      no_second_vote_in (LateVotes M C n₁ (s - 1)) vote = true} ⊆ LateVotes M C n₁ (s - 1) :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hSL₂ : {vote ∈ EarlyVotes M C n₂ (s - 1) |
      no_second_vote_in (LateVotes M C n₂ (s - 1)) vote = true} ⊆ LateVotes M C n₂ (s - 1) :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hRoots₂₁ : RootsNameBlocksIn ((M.fg_to_ac n₂).tree ∪ (M.fg_to_ac n₁).tree) := by
    rw [Finset.union_comm]
    exact hRoots
  by_contra hne
  have hdisj : Disjoint
      (supportersOf (M.fg_to_ac n₁)
        {vote ∈ EarlyVotes M C n₁ (s - 1) | no_second_vote_in (LateVotes M C n₁ (s - 1)) vote = true}
        {vote ∈ EarlyVotes M C n₁ (s - 1) | no_second_vote_in (LateVotes M C n₁ (s - 1)) vote = true}
        (s - 1) C₁)
      (supportersOf (M.fg_to_ac n₂)
        {vote ∈ EarlyVotes M C n₂ (s - 1) | no_second_vote_in (LateVotes M C n₂ (s - 1)) vote = true}
        {vote ∈ EarlyVotes M C n₂ (s - 1) | no_second_vote_in (LateVotes M C n₂ (s - 1)) vote = true}
        (s - 1) C₂) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact hne (compatible_of_common_supporter C₁ C₂ v hRoots hPL₂ hReach₁₂ hv₁ hv₂)
  have hc₂ := Finset.card_le_card (Finset.union_subset
    (supportersOf_subset_participants_of_reach C₁ _ hPL₂ hReach₁₂)
    (supportersOf_support_subset_participants (M.fg_to_ac n₂) (s - 1) C₂ _ _ hSL₂))
  have hc₁ := Finset.card_le_card (Finset.union_subset
    (supportersOf_support_subset_participants (M.fg_to_ac n₁) (s - 1) C₁ _ _ hSL₁)
    (supportersOf_subset_participants_of_reach C₂ _ hPL₁ hReach₂₁))
  rw [Finset.card_union_of_disjoint hdisj] at hc₁ hc₂
  rw [voters_count_eq] at hel₁ hel₂
  omega

/-- A supporter of `B` at the first node is a voter among the second node's late votes, when every
early vote of the first node is among the second node's late votes, or two late votes of its validator
are (the form of `supportersOf_subset_participants_of_reach` whose reach concludes into `LateVotes`).

The variables:
- `M`: the model; `C`: the configuration; `n₁`, `n₂`: the two node states; `s'`: the slot;
  `B`: the block.

Read aloud: the first node's supporters are voters among the second node's late votes. -/
theorem supportersOf_subset_participants_of_lateReach {M : GoldilocksModel V} {C : Config}
    {n₁ n₂ : M.N} {s' : Slot} (B : Block V)
    (hReach₁₂ : ∀ vote ∈ M.votesHeldSet n₁ s',
      (∃ y : Stamp, ResolvesAt M n₁ vote y ∧ occurrenceBefore (some y) (C.t_ s' + 2 * C.Δ) = true) →
      vote ∈ LateVotes M C n₂ s' ∨
        ∃ u₁ ∈ LateVotes M C n₂ s', ∃ u₂ ∈ LateVotes M C n₂ s',
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index) :
    supportersOf (M.fg_to_ac n₁)
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true}
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true} s' B ⊆
      participants (LateVotes M C n₂ s') := by
  intro v hv
  obtain ⟨x, hx, hxv, -⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv
  obtain ⟨hxp, y, hτ, hy⟩ := mem_earlyVotes.1 (Finset.mem_filter.1 hx).1
  rcases hReach₁₂ x hxp ⟨y, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨y, rfl, hy⟩⟩ with
    h | ⟨u₁, hu₁, -, -, -, hval, -⟩
  · exact (mem_participants_iff _ _).2 ⟨x, h, hxv⟩
  · exact (mem_participants_iff _ _).2 ⟨u₁, hu₁, hval.trans hxv⟩

/-- A validator that supports `B₁` at the first node and `B₂` at the second makes `B₁` and `B₂`
compatible, when every early vote of the first node is among the second node's late votes, or two late
votes of its validator are, and no two blocks of the two frame trees share a root (the form of
`compatible_of_common_supporter` whose reach concludes into `LateVotes`).

The variables:
- `M`: the model; `C`: the configuration; `n₁`, `n₂`: the two node states; `s'`: the slot;
  `B₁`, `B₂`: the blocks; `v`: the validator.

Read aloud: a common supporter makes the two blocks compatible. -/
theorem compatible_of_common_supporter_of_lateReach {M : GoldilocksModel V} {C : Config} {n₁ n₂ : M.N}
    {s' : Slot} (B₁ B₂ : Block V) (v : V)
    (hRoots : RootsNameBlocksIn ((M.fg_to_ac n₁).tree ∪ (M.fg_to_ac n₂).tree))
    (hReach₁₂ : ∀ vote ∈ M.votesHeldSet n₁ s',
      (∃ y : Stamp, ResolvesAt M n₁ vote y ∧ occurrenceBefore (some y) (C.t_ s' + 2 * C.Δ) = true) →
      vote ∈ LateVotes M C n₂ s' ∨
        ∃ u₁ ∈ LateVotes M C n₂ s', ∃ u₂ ∈ LateVotes M C n₂ s',
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    (hv₁ : v ∈ supportersOf (M.fg_to_ac n₁)
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true}
      {vote ∈ EarlyVotes M C n₁ s' | no_second_vote_in (LateVotes M C n₁ s') vote = true} s' B₁)
    (hv₂ : v ∈ supportersOf (M.fg_to_ac n₂)
      {vote ∈ EarlyVotes M C n₂ s' | no_second_vote_in (LateVotes M C n₂ s') vote = true}
      {vote ∈ EarlyVotes M C n₂ s' | no_second_vote_in (LateVotes M C n₂ s') vote = true} s' B₂) :
    B₁.compatible B₂ = true := by
  obtain ⟨x, hx, hxv, -, -, H₁, hH₁, hr₁, hB₁⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv₁
  obtain ⟨y, hy, hyv, -, -, H₂, hH₂, hr₂, hB₂⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hv₂
  obtain ⟨hxp, τ, hτ, hτc⟩ := mem_earlyVotes.1 (Finset.mem_filter.1 hx).1
  have hN := (Finset.mem_filter.1 hy).2
  simp only [no_second_vote_in, decide_eq_true_eq] at hN
  have hxy : x = y := by
    rcases hReach₁₂ x hxp ⟨τ, hτ, (occurrenceBefore_eq_true_iff _ _).2 ⟨τ, rfl, hτc⟩⟩ with
      h | ⟨u₁, hu₁, u₂, hu₂, hne, hval₁, hval₂⟩
    · rcases hN x h with h' | h'
      · exact h'
      · exact absurd (hxv.trans hyv.symm) h'
    · have e₁ : u₁ = y := (hN u₁ hu₁).resolve_right
        (fun h' => h' (hval₁.trans (hxv.trans hyv.symm)))
      have e₂ : u₂ = y := (hN u₂ hu₂).resolve_right
        (fun h' => h' (hval₂.trans (hxv.trans hyv.symm)))
      exact absurd (e₁.trans e₂.symm) hne
  subst hxy
  have hH : H₁ = H₂ := hRoots H₁ (Finset.mem_union_left _ hH₁) H₂ (Finset.mem_union_right _ hH₂)
    (hr₁.trans hr₂.symm)
  subst hH
  exact (compatible_iff _ _).2 (ancestorEq_compatible hB₁ hB₂)

/-- **Lemma 30's helper form, the reach concluding into the late votes.** Two confirmation updates of
slot `s ≥ 1` from the node states `n₁` and `n₂`, saving `C₁` and `C₂`, save compatible blocks, when no
two blocks of the two frame trees share a root, and every vote of either node resolving strictly before
`C.t_ (s − 1) + 2 · C.Δ` is among the other node's votes stamped strictly before `C.t_ (s − 1) + 6 · C.Δ`
(`LateVotes`), or two such votes of its validator are. Lemma 30's proof reads the stamp bound only on
the votes the reach places in the other node, so the reach into `LateVotes` stands in for Lemma 30's
`hLate₁`, `hLate₂`; Lemma 30's own text is unchanged.

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n₁`, `n₁'`, `n₂`, `n₂'`: the node
  states before and after the two updates; `t₁`, `t₂`: their times; `s`: the slot;
  `C₁`, `C₂`: the saved confirmations.

Read aloud: two updates of one slot whose early votes reach each other's late votes save blocks of one
chain. -/
theorem lem30_saved_confirmations_compatible_of_lateReach [RootOrder] {M : GoldilocksModel V} (F : Facts M)
    {C : Config} {P : Provisional V} {n₁ n₁' n₂ n₂' : M.N} {t₁ t₂ : Time} {s : Slot}
    (C₁ C₂ : Block V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- no two blocks of the two frame trees share a root
    (hRoots : RootsNameBlocksIn ((M.fg_to_ac n₁).tree ∪ (M.fg_to_ac n₂).tree))
    -- every early vote of `n₁` is among `n₂`'s late votes, or two late votes of its validator are
    (hReach₁₂ : ∀ vote ∈ M.votesHeldSet n₁ (s - 1),
      (∃ y : Stamp, ResolvesAt M n₁ vote y ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ LateVotes M C n₂ (s - 1) ∨
        ∃ u₁ ∈ LateVotes M C n₂ (s - 1), ∃ u₂ ∈ LateVotes M C n₂ (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- every early vote of `n₂` is among `n₁`'s late votes, or two late votes of its validator are
    (hReach₂₁ : ∀ vote ∈ M.votesHeldSet n₂ (s - 1),
      (∃ y : Stamp, ResolvesAt M n₂ vote y ∧
        occurrenceBefore (some y) (C.t_ (s - 1) + 2 * C.Δ) = true) →
      vote ∈ LateVotes M C n₁ (s - 1) ∨
        ∃ u₁ ∈ LateVotes M C n₁ (s - 1), ∃ u₂ ∈ LateVotes M C n₁ (s - 1),
          u₁ ≠ u₂ ∧ u₁.val_index = vote.val_index ∧ u₂.val_index = vote.val_index)
    -- the update from `n₁` leaves `n₁'` and saves `C₁`
    (hUpdate₁ : ConfirmationUpdated M C P n₁ t₁ s n₁')
    (hSaved₁ : n₁'.savedConfirmation (s - 1) = some C₁)
    -- the update from `n₂` leaves `n₂'` and saves `C₂`
    (hUpdate₂ : ConfirmationUpdated M C P n₂ t₂ s n₂')
    (hSaved₂ : n₂'.savedConfirmation (s - 1) = some C₂) :
    -- then `C₁` and `C₂` are compatible
    C₁.compatible C₂ = true := by
  have hRoots₁ : RootsNameBlocksIn (M.fg_to_ac n₁).tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_left _ hB) B' (Finset.mem_union_left _ hB') h
  have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac n₂).tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_right _ hB) B' (Finset.mem_union_right _ hB') h
  have hel₁ := confirmationUpdated_saved_count F hs hRoots₁ hUpdate₁ hSaved₁
  have hel₂ := confirmationUpdated_saved_count F hs hRoots₂ hUpdate₂ hSaved₂
  rw [equivocators_support_eq_empty _ _ earlyVotes_subset_lateVotes, Finset.card_empty,
    zero_add] at hel₁ hel₂
  have hSL₁ : {vote ∈ EarlyVotes M C n₁ (s - 1) |
      no_second_vote_in (LateVotes M C n₁ (s - 1)) vote = true} ⊆ LateVotes M C n₁ (s - 1) :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  have hSL₂ : {vote ∈ EarlyVotes M C n₂ (s - 1) |
      no_second_vote_in (LateVotes M C n₂ (s - 1)) vote = true} ⊆ LateVotes M C n₂ (s - 1) :=
    fun vote hv => earlyVotes_subset_lateVotes (Finset.mem_filter.1 hv).1
  by_contra hne
  have hdisj : Disjoint
      (supportersOf (M.fg_to_ac n₁)
        {vote ∈ EarlyVotes M C n₁ (s - 1) | no_second_vote_in (LateVotes M C n₁ (s - 1)) vote = true}
        {vote ∈ EarlyVotes M C n₁ (s - 1) | no_second_vote_in (LateVotes M C n₁ (s - 1)) vote = true}
        (s - 1) C₁)
      (supportersOf (M.fg_to_ac n₂)
        {vote ∈ EarlyVotes M C n₂ (s - 1) | no_second_vote_in (LateVotes M C n₂ (s - 1)) vote = true}
        {vote ∈ EarlyVotes M C n₂ (s - 1) | no_second_vote_in (LateVotes M C n₂ (s - 1)) vote = true}
        (s - 1) C₂) := by
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact hne (compatible_of_common_supporter_of_lateReach C₁ C₂ v hRoots hReach₁₂ hv₁ hv₂)
  have hc₂ := Finset.card_le_card (Finset.union_subset
    (supportersOf_subset_participants_of_lateReach C₁ hReach₁₂)
    (supportersOf_support_subset_participants (M.fg_to_ac n₂) (s - 1) C₂ _ _ hSL₂))
  have hc₁ := Finset.card_le_card (Finset.union_subset
    (supportersOf_support_subset_participants (M.fg_to_ac n₁) (s - 1) C₁ _ _ hSL₁)
    (supportersOf_subset_participants_of_lateReach C₂ hReach₂₁))
  rw [Finset.card_union_of_disjoint hdisj] at hc₁ hc₂
  rw [voters_count_eq] at hel₁ hel₂
  omega

/-- **Lemma 35 over the record.** The update of slot `s` keeps every lock entry of `n` whose deadline
is after `t`, and every other entry of `n'` has the deadline `C.t_ (s − 1 + C.k) + 5 · C.Δ`, is on a
non-genesis block of the frame's tree on the saved confirmation's chain, and that block is a fast
block of `n'` or passes the slow test (the record form of `lem35_update_confirmation_lock_entries`).

The variables:
- `M`: the model; `C`, `P`: the parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: the update keeps the unexpired locks and adds only the lock of a tested block. -/
theorem lem35_update_confirmation_lock_entries [RootOrder] {M : GoldilocksModel V} {C : Config}
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    -- the confirmation update of slot `s` leaves `n'`
    (hUpdate : ConfirmationUpdated M C P n t s n') :
    (∀ e ∈ n.lockEntries, t < e.d → e ∈ n'.lockEntries) ∧
    ∀ e ∈ n'.lockEntries, e ∈ n.lockEntries ∨
      (e.d = C.t_ (s - 1 + C.k) + 5 * C.Δ ∧ e.B ∈ (M.fg_to_ac n).tree ∧ e.B ≠ Block.genesis ∧
        (∃ C' : Block V, n'.savedConfirmation (s - 1) = some C' ∧ e.B.AncestorEq C') ∧
        (e.B ∈ n'.fastBlocks ∨ M.slow_test C n (s - 1) e.B = true)) := by
  refine ⟨confirmationUpdated_entries_keep hUpdate, fun e he => ?_⟩
  rcases confirmationUpdated_entries_cases hUpdate e he with h | ⟨hs, H, hS, hv, hL, hd⟩
  · exact Or.inl h.1
  · obtain ⟨-, -, -, hv0⟩ := confirmationUpdated_saved_some hs hUpdate hS
    obtain ⟨hT, hg, hBH, hft⟩ := hL
    refine Or.inr ⟨hd, hT, hg, ⟨H, hS, hBH⟩, ?_⟩
    rcases hft with hf | hsl
    · exact Or.inl (((hv0 hv).2.1 e.B).2 ⟨hT, hg, hBH, hf⟩)
    · exact Or.inr hsl

/-- **Lemma 36 over the record**, the statement form of
`GoldilocksCorrectness.Record.Proofs.Routines.lem36_confirmed_ancestor_early_supporters`.

The variables:
- `M`: the model; `F`: its facts; `C`, `P`: the parameters; `n`, `n'`: the node states before and
  after; `t`: the time; `s`: the slot; `C'`: the saved confirmation; `L`: the block.

Read aloud: a confirmed block's ancestors have early supporters. -/
theorem lem36_confirmed_ancestor_early_supporters [RootOrder] {M : GoldilocksModel V}
    (F : Facts M) {C : Config} {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot}
    (C' L : Block V)
    (hs : 1 ≤ s)
    (hRoots : RootsNameBlocksIn (M.fg_to_ac n).tree)
    (hLate : ∀ vote ∈ M.votesHeldSet n (s - 1), ∃ τ : Stamp, n.voteStamp vote = some τ ∧
      τ < ((C.t_ (s - 1) + 6 * C.Δ : Time) : Stamp))
    (hUpdate : ConfirmationUpdated M C P n t s n')
    (hSaved : n'.savedConfirmation (s - 1) = some C')
    (hLC : L.AncestorEq C') :
    ∃ Sup : Finset V, (∀ u ∈ Sup, EarlySupporterOf M C n (s - 1) L u) ∧
      M.voters_count (M.votesHeldSet n (s - 1)) < 2 * Sup.card ∧
      (L ∈ n'.fastBlocks → (P.committee (s - 1)).card ≤ 2 * Sup.card) :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem36_confirmed_ancestor_early_supporters F C' L hs
    hRoots hLate hUpdate hSaved hLC

/-- **Lemma 37 over the record.** When the slow test of `L` in the update of slot `s` passes,
`C.k − 1 ≤ s`, and every slot `s'` from `s + 1 − C.k` to `s − 1` has a saved confirmation `C'` in
the frame's tree of which `L` is an ancestor or which is `L` (the record form of
`lem37_slow_test_saved_confirmations`).

The variables:
- `M`: the model; `F`: its facts; `C`: the configuration; `n`: the node state; `s`: the slot;
  `L`: the block.

Read aloud: the slow test reads the saved confirmations. -/
theorem lem37_slow_test_saved_confirmations {M : GoldilocksModel V} (F : Facts M) (C : Config)
    (n : M.N) (s : Slot) (L : Block V)
    -- the slow test of `L` in the update of slot `s` passes
    (hSlow : M.slow_test C n s L = true) :
    C.k - 1 ≤ s ∧ ∀ s' : Slot, s + 1 - C.k ≤ s' → s' < s →
      ∃ C' : Block V, n.savedConfirmation s' = some C' ∧ C' ∈ (M.fg_to_ac n).tree ∧
        L.AncestorEq C' := by
  rw [F.rd.slow_test_eq, decide_eq_true_eq] at hSlow
  obtain ⟨hk, hall⟩ := hSlow
  refine ⟨hk, fun s' hj hjs => ?_⟩
  have hmem : s' ∈ M.slots_before s C.k := by
    rw [F.rd.slots_before_eq]
    simp only [Finset.map', Finset.mem_image, Finset.mem_range]
    have hjs' : @LT.lt ℕ _ s' s := hjs
    have hj' : @LE.le ℕ _ (s + 1 - C.k) s' := hj
    have hk' : @LE.le ℕ _ (C.k - 1) s := hk
    exact ⟨s' - (s + 1 - C.k), by omega, Nat.add_sub_of_le hj'⟩
  have h := hall s' hmem
  rw [F.rd.saved_extends_eq] at h
  cases hS : n.savedConfirmation s' with
  | none => simp [hS] at h
  | some C' =>
    simp only [hS, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨C', rfl, h⟩

/-! ## The revocation of the locks -/

/-- The revocation of slot `s' ≠ 0` keeps a live lock entry of `n` that fewer than half of the
committee oppose (the record form of the statement `revoke_locks_keeps_entry`).

The variables:
- `M`: the model; `F`: its facts; `P`: the provisional parameters; `n`, `n'`: the node states
  before and after; `t`: the time; `s'`: the slot; `e`: the entry.

Read aloud: a live lock fewer than half of the committee oppose survives the revocation. -/
theorem revoke_locks_keeps_entry {M : GoldilocksModel V} (F : Facts M) {P : Provisional V}
    {n n' : M.N} {t : Time} {s' : Slot} (e : M.LE)
    (hs' : s' ≠ 0) (hrev : LocksRevoked M P n t s' n')
    (he : e ∈ n.lockEntries) (hlive : M.is_live n t e = true) (hgen : e.B ≠ Block.genesis)
    (hopp : ∀ o : Finset V, OpponentsOf M n (M.votesHeldSet n (s' - 1))
      (M.equivocators (M.votesHeldSet n (s' - 1))) e.B o →
      2 * o.card < (P.committee (s' - 1)).card) :
    ∃ e' ∈ n'.lockEntries, e'.B = e.B ∧ e'.d = e.d :=
  GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_keeps_entry F e hs' hrev he hlive hgen
    hopp

/-- Under the facts, a validator with exactly one vote in a set of votes is not one of its
equivocators.

The variables:
- `M`: the model; `F`: its facts; `X`: the votes; `vote`: the vote; `v`: its validator.

Read aloud: a validator voting once does not equivocate. -/
theorem not_mem_equivocators_of_unique {M : GoldilocksModel V} (F : Facts M)
    {X : Finset (GoldfishVote V)} {vote : GoldfishVote V} {v : V}
    (hu : ∀ vote' ∈ X, vote'.val_index = v → vote' = vote) : v ∉ M.equivocators X := by
  rw [F.rd.equivocators_eq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, F.rd.equivocates_eq, F.rd.votes_by_eq,
    decide_eq_true_eq, not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.2 fun a ha b hb => ?_)
  rw [Finset.mem_filter] at ha hb
  rw [hu a ha.1 ha.2, hu b hb.1 hb.2]

/-- **Lemma 5 over the record.** After the revocation of slot `s ≥ 1`, every lock entry left is on a
block of the frame's tree compatible with `R`, when every member of `Hs` has exactly one vote of
the slot, it resolves and its head is a block of the frame's tree that is `R` or a descendant of
`R`, and the committee of slot `s − 1` is at most twice `Hs` (the record form of
`lem5_revoke_locks_entries_compatible`; the landed hypothesis that no two blocks of the frame's
tree share a root is not used by this form).

The variables:
- `M`: the model; `F`: its facts; `P`: the provisional parameters; `n`, `n'`: the node states
  before and after; `t`: the time; `s`: the slot; `R`: the majority block; `Hs`: the voters.

Read aloud: after the revocation, every lock is compatible with a half-committee's block. -/
theorem lem5_revoke_locks_entries_compatible {M : GoldilocksModel V} (F : Facts M)
    {P : Provisional V} {n n' : M.N} {t : Time} {s : Slot} (R : Block V) (Hs : Finset V)
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- each member of `Hs` has exactly one vote of the slot, it resolves, and its head is a block
    -- of the frame's tree that is `R` or a descendant of `R`
    (hHs : ∀ v ∈ Hs, VotesOnceInPoolFor M n (s - 1) R v)
    -- the slot-`(s − 1)` committee is at most twice `Hs`
    (hHalf : (P.committee (s - 1)).card ≤ 2 * Hs.card)
    -- the revocation of slot `s` leaves `n'`
    (hRevoke : LocksRevoked M P n t s n') :
    ∀ e ∈ n'.lockEntries, e.B ∈ (M.fg_to_ac n).tree ∧ e.B.compatible R = true := by
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exact absurd h0 (Nat.one_le_iff_ne_zero.1 hs)
  intro e he
  obtain ⟨e₀, -, -, -, hmt⟩ := h1 e he
  obtain ⟨hT, -, -, o, ho, hcard⟩ := hmt.1
  refine ⟨hT, ?_⟩
  by_contra hcompat
  have hconf : e.B.conflicts R = true := (conflicts_iff _ _).2 hcompat
  have hsub : Hs ⊆ o := by
    intro v hv
    obtain ⟨vote, hvote, hval, ⟨x, hτ⟩, ⟨H, hH, hr, hRH⟩, hu⟩ := hHs v hv
    refine (ho v).2 ⟨not_mem_equivocators_of_unique F hu, vote, hvote, hval, ⟨x, hτ⟩,
      H, hH, hr, ?_⟩
    rw [conflicts_comm]
    exact conflicts_of_ancestorEq_conflicts hRH hconf
  have h1 := Finset.card_le_card hsub
  omega

/-- **Lemma 38 over the record.** After the revocation of slot `s ≥ 1`, every lock entry left comes
from a lock entry of `n` live at `t`, with the same deadline, moved to a block of the frame's tree
that is the entry's block or an ancestor of it (the record form of
`lem38_revoke_locks_entries_moved`).

The variables:
- `M`: the model; `P`: the provisional parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: a lock after the revocation is a live lock of `n` moved back on its chain. -/
theorem lem38_revoke_locks_entries_moved {M : GoldilocksModel V} {P : Provisional V}
    {n n' : M.N} {t : Time} {s : Slot}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the revocation of slot `s` leaves `n'`
    (hRevoke : LocksRevoked M P n t s n') :
    ∀ e' ∈ n'.lockEntries, ∃ e ∈ n.lockEntries, M.is_live n t e = true ∧ e'.d = e.d ∧
      e'.B.AncestorEq e.B ∧ e'.B ∈ (M.fg_to_ac n).tree := by
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exact absurd h0 (Nat.one_le_iff_ne_zero.1 hs)
  intro e' he'
  obtain ⟨e, he, hl, hd, hmt⟩ := h1 e' he'
  exact ⟨e, he, hl, hd, hmt.1.2.2.1, hmt.1.1⟩

/-! ## At the spec's model -/

/-- The landed statement `fast_blocks_ancestorEq_saved`, recovered from its record form at the
spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n` whose
frame's tree has no two blocks sharing a root and whose lock entries all have a deadline after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem fast_blocks_ancestorEq_saved_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (C' : Block V),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.fast_blocks_ancestorEq_saved V _ _ _ C P n.A A' (fg_to_ac n.S) t s C') := by
  intro C P n A' t s C' hH hs hUpdate hSaved
  exact fast_blocks_ancestorEq_saved hs (confirmationUpdated_at_node C P n t s A' hH hUpdate) hSaved

/-- The landed statement `lem77_update_confirmation_extends_voter_majority_chain`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose lock entries all have a deadline after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem lem77_update_confirmation_extends_voter_majority_chain_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V),
      (∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem77_update_confirmation_extends_voter_majority_chain V _ _ _ C P n.A A' (fg_to_ac n.S) t s B Hs) := by
  intro C P n A' t s B Hs hE hs hRoots hF hPathF hHs hSlot hVoters hUpdate
  exact lem77_update_confirmation_extends_voter_majority_chain goldilocksFacts
    (n' := { n with A := A' }) B Hs hs hRoots hF hPathF
    (fun v hv => (goldilocks_earlySupporterOf C n (s - 1) B v hRoots).1 (hHs v hv)) hSlot hVoters
    (confirmationUpdated_at_node C P n t s A' ⟨hRoots, hE⟩ hUpdate)

/-- The landed statement `saved_confirmation_F_ancestorEq`, recovered from its record form at the
spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n` whose
frame's tree has no two blocks sharing a root and whose lock entries all have a deadline after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem saved_confirmation_F_ancestorEq_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.saved_confirmation_F_ancestorEq V _ _ _ C P n.A A' (fg_to_ac n.S) t s) := by
  intro C P n A' t s hH hs hUpdate
  exact saved_confirmation_F_ancestorEq hs (confirmationUpdated_at_node C P n t s A' hH hUpdate)

/-- The landed statement `lem25_update_confirmation_confirms_voter_majority_block`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose lock entries all have a deadline after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem lem25_update_confirmation_confirms_voter_majority_block_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V),
      (∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem25_update_confirmation_confirms_voter_majority_block V _ _ _ C P n.A A' (fg_to_ac n.S) t s B Hs) := by
  intro C P n A' t s B Hs hE hs hRoots hBne hF hPathF hHs hSlot hVoters hNoVeto hUpdate
  exact lem25_update_confirmation_confirms_voter_majority_block goldilocksFacts
    (n' := { n with A := A' }) B Hs hs hRoots hBne hF hPathF
    (fun v hv => (goldilocks_earlyVoteOnceFor C n (s - 1) B v hRoots).1 (hHs v hv)) hSlot hVoters
    hNoVeto (confirmationUpdated_at_node C P n t s A' ⟨hRoots, hE⟩ hUpdate)

/-- The landed statement `lem28_update_confirmation_fast_locks_voter_majority_block`, recovered
from its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of
every node state `n` whose lock entries all have a deadline after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem lem28_update_confirmation_fast_locks_voter_majority_block_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (B : Block V) (Hs : Finset V),
      (∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem28_update_confirmation_fast_locks_voter_majority_block V _ _ _ C P n.A A' (fg_to_ac n.S) t s B Hs) := by
  intro C P n A' t s B Hs hE hs hRoots hBne hF hPathF hHs hSlot hVoters hHalf hNoVeto hUpdate
  obtain ⟨hfast, e, he, hB, hd⟩ := lem28_update_confirmation_fast_locks_voter_majority_block
    goldilocksFacts (n' := { n with A := A' }) B Hs hs hRoots hBne hF hPathF
    (fun v hv => (goldilocks_earlyVoteOnceFor C n (s - 1) B v hRoots).1 (hHs v hv)) hSlot hVoters
    hHalf hNoVeto (confirmationUpdated_at_node C P n t s A' ⟨hRoots, hE⟩ hUpdate)
  have hee : e = LockEntry.mk B (C.t_ (s - 1 + C.k) + 5 * C.Δ) := lockEntry_eq_mk hB hd
  exact ⟨hfast, hee ▸ he⟩

/-- The landed statement `lem30_saved_confirmations_compatible`, recovered from its record form at
the spec's model, at the AC states `n1.A`, `n2.A` and the frames `fg_to_ac n1.S`, `fg_to_ac n2.S`
of two node states whose lock entries all have a deadline after the times of the updates.

Read aloud: the landed statement holds at every two such node states. -/
theorem lem30_saved_confirmations_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n1 : NodeState V) (A₁' : ACState V) (n2 : NodeState V) (A₂' : ACState V) (t₁ t₂ : Time) (s : Slot) (C₁ C₂ : Block V),
      ((∀ e ∈ n1.A.lock_entries, t₁ < e.d) ∧ ∀ e ∈ n2.A.lock_entries, t₂ < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem30_saved_confirmations_compatible V _ _ _ C P n1.A A₁' n2.A A₂' (fg_to_ac n1.S) (fg_to_ac n2.S) t₁ t₂ s C₁ C₂) := by
  intro C P n1 A₁' n2 A₂' t₁ t₂ s C₁ C₂ hE hs hRoots hLate₁ hLate₂ hReach₁₂ hReach₂₁ hUpdate₁
    hSaved₁ hUpdate₂ hSaved₂
  have hR₁ : RootsNameBlocksIn (fg_to_ac n1.S).tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_left _ hB) B' (Finset.mem_union_left _ hB') h
  have hR₂ : RootsNameBlocksIn (fg_to_ac n2.S).tree := fun B hB B' hB' h =>
    hRoots B (Finset.mem_union_right _ hB) B' (Finset.mem_union_right _ hB') h
  exact lem30_saved_confirmations_compatible goldilocksFacts (n₁ := n1) (n₂ := n2)
    (n₁' := { n1 with A := A₁' }) (n₂' := { n2 with A := A₂' }) C₁ C₂ hs hRoots hLate₁ hLate₂
    (fun vote hv ⟨y, hy, ho⟩ => hReach₁₂ vote hv ⟨y, (goldilocks_resolvesAt n1 vote y hR₁).2 hy, ho⟩)
    (fun vote hv ⟨y, hy, ho⟩ => hReach₂₁ vote hv ⟨y, (goldilocks_resolvesAt n2 vote y hR₂).2 hy, ho⟩)
    (confirmationUpdated_at_node C P n1 t₁ s A₁' ⟨hR₁, hE.1⟩ hUpdate₁) hSaved₁
    (confirmationUpdated_at_node C P n2 t₂ s A₂' ⟨hR₂, hE.2⟩ hUpdate₂) hSaved₂

/-- The landed statement `lem35_update_confirmation_lock_entries`, recovered from its record form
at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n`
whose frame's tree has no two blocks sharing a root and whose lock entries all have a deadline
after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem lem35_update_confirmation_lock_entries_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      (RootsNameBlocksIn (fg_to_ac n.S).tree ∧ ∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem35_update_confirmation_lock_entries V _ _ _ C P n.A A' (fg_to_ac n.S) t s) := by
  intro C P n A' t s hH hUpdate
  obtain ⟨h1, h2⟩ := lem35_update_confirmation_lock_entries
    (confirmationUpdated_at_node C P n t s A' hH hUpdate)
  exact ⟨fun e he => h1 e he (hH.2 e he), h2⟩

/-- The landed statement `lem36_confirmed_ancestor_early_supporters`, recovered from its record form
at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n`
whose lock entries all have a deadline after `t`.

Read aloud: the landed statement holds at every such node state. -/
theorem lem36_confirmed_ancestor_early_supporters_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (C' L : Block V),
      (∀ e ∈ n.A.lock_entries, t < e.d) →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters V _ _ _ C P n.A A' (fg_to_ac n.S) t s C' L) := by
  intro C P n A' t s C' L hE hs hRoots hLate hUpdate hSaved hLC
  obtain ⟨Sup, hSup, hV, hFast⟩ := lem36_confirmed_ancestor_early_supporters goldilocksFacts
    (n' := { n with A := A' }) C' L hs hRoots hLate
    (confirmationUpdated_at_node C P n t s A' ⟨hRoots, hE⟩ hUpdate) hSaved hLC
  exact ⟨Sup, fun u hu => (goldilocks_earlySupporterOf C n (s - 1) L u hRoots).2 (hSup u hu), hV,
    hFast⟩

/-- The landed statement `lem37_slow_test_saved_confirmations`, recovered from its record form at
the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n`.

Read aloud: the landed statement holds at every node state. -/
theorem lem37_slow_test_saved_confirmations_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (n : NodeState V) (s : Slot) (L : Block V),
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem37_slow_test_saved_confirmations V _ _ _ C n.A (fg_to_ac n.S) s L) := by
  intro C n s L hSlow
  exact lem37_slow_test_saved_confirmations goldilocksFacts C n s L hSlow

/-- The landed statement `revoke_locks_keeps_entry`, recovered from its record form at the spec's
model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n` satisfying the
spec's node invariant.

Read aloud: the landed statement holds at every node state satisfying the invariant. -/
theorem revoke_locks_keeps_entry_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (A' : ACState V) (t : Time) (s' : Slot) (e : LockEntry V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.revoke_locks_keeps_entry V _ _ _ P n.A A' (fg_to_ac n.S) t s' e) := by
  intro C P X n A' t s' e hI hs' hrev he hlive hgen hopp
  exact GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_keeps_entry_recovered C P X n A'
    t s' e hI hs' hrev he hlive hgen hopp

/-- The landed statement `lem5_revoke_locks_entries_compatible`, recovered from its record form at
the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n`.

Read aloud: the landed statement holds at every node state. -/
theorem lem5_revoke_locks_entries_compatible_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot) (R : Block V) (Hs : Finset V),
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem5_revoke_locks_entries_compatible V _ _ _ P n.A A' (fg_to_ac n.S) t s R Hs) := by
  intro P n A' t s R Hs hs hRoots hHs hHalf hRevoke
  exact lem5_revoke_locks_entries_compatible goldilocksFacts (n' := { n with A := A' }) R Hs hs
    (fun v hv => (goldilocks_votesOnceInPoolFor n (s - 1) R v hRoots).1 (hHs v hv)) hHalf
    (locksRevoked_at_node P n t s A' hRoots (Nat.one_le_iff_ne_zero.1 hs) hRevoke)

/-- The landed statement `lem38_revoke_locks_entries_moved`, recovered from its record form at the
spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node state `n` whose
frame's tree has no two blocks sharing a root.

Read aloud: the landed statement holds at every such node state. -/
theorem lem38_revoke_locks_entries_moved_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      RootsNameBlocksIn (fg_to_ac n.S).tree →
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved V _ _ _ P n.A A' (fg_to_ac n.S) t s) := by
  intro P n A' t s hR hs hRevoke
  exact lem38_revoke_locks_entries_moved hs
    (locksRevoked_at_node P n t s A' hR (Nat.one_le_iff_ne_zero.1 hs) hRevoke)

end GoldilocksCorrectness.Record.Statements.Routines
