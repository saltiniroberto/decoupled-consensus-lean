module
public import GoldilocksCorrectness.Record.ModelSpellings

@[expose] public section

/-!
# The facts of the readers derived from a node state

`ReaderFacts M` holds, for a model `M`, the defining equation of each reader the record derives
from a node state or from the objects, one field per reader: the reader on the left, on the right
what it answers, written with the record's node readers (`n.tree`, `n.finalized`,
`n.lockEntries`, `n.sentTarget h`, …) and the other derived readers (`M.fg_to_ac n`,
`M.is_live n t e`, …). A reader the spec computes from a part of the node state is taken on the
whole node state `n`; one the spec computes from the objects alone (a block, a set of votes, the
record `Φ : Frame V`) keeps its arguments. Four fields restate the library's theorems on the
readers of the anti-slashing record (`finality_pair_some`, `own_lock_cases`,
`height_pair_vote_cases`, `height_pair_timeout`), each over the node state; three are the
library's characterisations of a reader by an `↔` (`attestation_well_formed_iff`,
`block_well_formed_iff`) or by its cases (`saved_extends_eq`, `ac_confirmed_eq`, `advance_eq`,
`awake_since_eq`, written as a `match` or an `if`).

The readers of a node state that read the node's stored chain states or its stored greatest
chain-state height (`fg_contest`, `head_height_floor`, `get_fc_root`, `is_viable`,
`proposal_attestations`, `block_admissible`) have no field here: the record reads a chain state as
the block's own, `M.chainStateOf C B`, and the greatest height as `hMax M C n`, and the spec's
readers equal those forms only on a node state whose stored values are the computed ones. This
file holds the structure only.
-/

set_option autoImplicit false
-- the hypotheses of the fields are named, as in the theorems the fields restate
set_option linter.unusedVariables false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block Attestation AttestationContent
  GoldfishVote Frame FinalityPair HeightPair BlockId Height Slot Time)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the readers derived from a node state or from the objects.

Read aloud: each reader the model `M` derives answers what the spec's reader of the same name
answers, read on the node state. -/
structure ReaderFacts (M : GoldilocksModel V) : Prop where
  /-- The definition of the reader `has_viable_descendant`.

      Read aloud: `B` has a viable descendant in `n` when some block of `n`'s tree that is `B`
      or a descendant of `B` is viable in `n`. -/
  has_viable_descendant_eq : ∀ (n : M.N) (B : Block V),
      M.has_viable_descendant n B = decide (∃ B' ∈ n.tree, B.ancestorEq B' ∧ M.is_viable n B')
  /-- The definition of the reader `fg_to_ac`.

      Read aloud: the record `M.fg_to_ac n` has as its tree the blocks of `n`'s tree that are
      `n`'s finalized block or a descendant of it; as its root the fgroot `M.get_fc_root n`; as
      its viable heads the blocks of that tree that are the fgroot or a descendant of it and are
      viable in `n`; and as its finalized block `n.finalized`. -/
  fg_to_ac_eq : ∀ (n : M.N),
      M.fg_to_ac n = Frame.mk (tree := {B ∈ n.tree | n.finalized.ancestorEq B})
        (fc_root := M.get_fc_root n)
        (viable_heads := {B ∈ {B ∈ n.tree | n.finalized.ancestorEq B} |
          (M.get_fc_root n).ancestorEq B && M.is_viable n B})
        (F := n.finalized)
  /-- The definition of the reader `attestations_on_chain` at the genesis block.

      Read aloud: no attestation is included on the genesis block's chain. -/
  attestations_on_chain_genesis : M.attestations_on_chain (Block.genesis : Block V) = []
  /-- The definition of the reader `attestations_on_chain` at a block other than the genesis
      block.

      Read aloud: the attestations on a block's chain are those it includes, then those on its
      parent's chain. -/
  attestations_on_chain_node : ∀ (p : Block V) (s : Slot) (r : BlockId)
      (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V),
      M.attestations_on_chain (Block.node p s r votes support ats v) =
        ats ++ M.attestations_on_chain p
  /-- The definition of the reader `on_chain`.

      Read aloud: `M.on_chain a H` answers whether `a` is among the attestations on `H`'s
      chain. -/
  on_chain_eq : ∀ (a : Attestation V) (H : Block V),
      M.on_chain a H = decide (a ∈ M.attestations_on_chain H)
  /-- When `finality_pair` returns a pair, it is `(h_j, J)`, `h_F < h_j`, and the node's
      anti-slashing record holds at `h_j` no target other than `J`, no timeout and no lock other
      than `J`.

      Read aloud: a finality pair the node allows names the justification it was asked about,
      has a source height less than its own, and the node has signed nothing at that height that
      names another block or a timeout. -/
  finality_pair_some : ∀ {n : M.N} {h_j : Height} {J : BlockId} {h_F : Height} {p : FinalityPair},
      M.finality_pair n h_j J h_F = some p →
        p = ⟨h_j, J⟩ ∧ h_F < h_j ∧ (∀ T : BlockId, n.sentTarget h_j = some T → T = J) ∧
          n.sentTimeout h_j = false ∧ (∀ T : BlockId, n.sentLock h_j = some T → T = J)
  /-- The lock `own_lock` reads at `h` is the node's lock at `h`, or the target of the finality
      pair `fp` when `fp` is at `h`.

      Read aloud: the lock the height pair reads at `h` is the node's own lock at `h`, or the
      block of the finality pair when that pair is at `h`. -/
  own_lock_cases : ∀ (n : M.N) (h : Height) (fp : Option FinalityPair),
      M.own_lock n h fp = n.sentLock h ∨
        ∃ q : FinalityPair, fp = some q ∧ q.hf = h ∧ M.own_lock n h fp = some q.Tf
  /-- A height pair `height_pair` computes from the source `(h_c, T_c)` that is a vote is at
      `h_c` and names `T_c`; a target vote is cast only when the node holds no timeout at `h_c`
      and the lock read at `h_c` is unset or `T_c`; a timeout only when the node holds a timeout
      at `h_c` or the lock read at `h_c` is unset.

      Read aloud: the vote the node computes from a source is at the source's height and names
      the source's block, and a target vote or a timeout is cast only when the node's own
      signatures at that height allow it. -/
  height_pair_vote_cases : ∀ {n : M.N} {h_c : Height} {T_c : BlockId}
      {fp : Option FinalityPair} {h : Height} {T : BlockId} {τ : Bool},
      M.height_pair n (some (h_c, T_c)) fp = .vote h T τ →
        h = h_c ∧ T = T_c ∧
          (τ = false → n.sentTimeout h_c = false ∧
            ∀ L : BlockId, M.own_lock n h_c fp = some L → L = T_c) ∧
          (τ = true → n.sentTimeout h_c = true ∨ M.own_lock n h_c fp = none)
  /-- A timeout `height_pair` computes from the source `(h_c, T_c)` is cast only when the node
      holds a timeout at `h_c`, or a target at `h_c` for a block other than `T_c`.

      Read aloud: the node times out at a source's height only when it already timed out there
      or already voted there for another block. -/
  height_pair_timeout : ∀ {n : M.N} {h_c : Height} {T_c : BlockId}
      {fp : Option FinalityPair} {h : Height} {T : BlockId},
      M.height_pair n (some (h_c, T_c)) fp = .vote h T true →
        n.sentTimeout h_c = true ∨ ∃ T' : BlockId, n.sentTarget h_c = some T' ∧ T' ≠ T_c
  /-- The definition of the reader `already_sent`.

      Read aloud: `M.already_sent n h T τ` answers whether the node sent an attestation at the
      height `h` that is a target vote, when `τ` is false, or names `T`. -/
  already_sent_eq : ∀ (n : M.N) (h : Height) (T : BlockId) (τ : Bool),
      M.already_sent n h T τ = decide (∃ b ∈ n.sentAttestations, b.h = h ∧ (!τ ∨ b.T = T))
  /-- The definition of the reader `votesHeldSet`.

      Read aloud: the set of the node's votes of slot `s` is the set of the members of its list
      of votes of slot `s`. -/
  votesHeldSet_eq : ∀ (n : M.N) (s : Slot), M.votesHeldSet n s = (n.votesHeld s).toFinset
  /-- The definition of the reader `ac_valid_payload`.

      Read aloud: `B`'s payload is valid when every Goldfish vote it includes has the slot
      `B.slot − 1`, every support vote it includes is one of its Goldfish votes, and the validator
      of every Goldfish vote it includes is in the committee of slot `B.slot − 1`. -/
  ac_valid_payload_eq : ∀ (P : Provisional V) (B : Block V),
      M.ac_valid_payload P B =
        decide ((∀ vote ∈ B.votes, vote.slot = B.slot - 1) ∧
          (∀ vote ∈ B.support_votes, vote ∈ B.votes) ∧
          ∀ vote ∈ B.votes, vote.val_index ∈ P.committee (B.slot - 1))
  /-- The definition of the reader `included_votes`.

      Read aloud: the votes included at slot `s` are the slot-`(s − 1)` Goldfish votes of the
      slot-`s` blocks of `Φ.tree`. -/
  included_votes_eq : ∀ (Φ : Frame V) (s : Slot),
      M.included_votes Φ s =
        {B ∈ Φ.tree | B.slot = s}.biUnion fun B => {vote ∈ B.votes.toFinset | vote.slot = s - 1}
  /-- The definition of the reader `included_support_votes`.

      Read aloud: the support votes included at slot `s` are the slot-`(s − 1)` support votes of
      the slot-`s` blocks of `Φ.tree`. -/
  included_support_votes_eq : ∀ (Φ : Frame V) (s : Slot),
      M.included_support_votes Φ s =
        {B ∈ Φ.tree | B.slot = s}.biUnion fun B =>
          {vote ∈ B.support_votes.toFinset | vote.slot = s - 1}
  /-- The definition of the reader `is_live`.

      Read aloud: the lock entry `e` is live at `t` in `n` when `t` is strictly before its
      deadline and its block is in the tree of `M.fg_to_ac n`. -/
  is_live_eq : ∀ (n : M.N) (t : Time) (e : M.LE),
      M.is_live n t e = (decide (t < e.d) && decide (e.B ∈ (M.fg_to_ac n).tree))
  /-- The definition of the reader `is_locked`.

      Read aloud: `B'` is locked at `t` in `n` when some lock entry of `n` live at `t` has a
      block that is `B'` or a descendant of `B'`. -/
  is_locked_eq : ∀ (n : M.N) (t : Time) (B' : Block V),
      M.is_locked n t B' =
        decide (∃ e ∈ n.lockEntries, M.is_live n t e = true ∧ B'.ancestorEq e.B = true)
  /-- The definition of the reader `live_lock_vetoes`.

      Read aloud: a live lock of `n` vetoes `C` at `t` when some lock entry of `n` live at `t` has
      a block that conflicts with `C`. -/
  live_lock_vetoes_eq : ∀ (n : M.N) (t : Time) (C : Block V),
      M.live_lock_vetoes n t C =
        decide (∃ e ∈ n.lockEntries, M.is_live n t e = true ∧ e.B.conflicts C = true)
  /-- The definition of the reader `votes_by`.

      Read aloud: `v`'s votes in `votes` are the votes of `votes` whose validator is `v`. -/
  votes_by_eq : ∀ (votes : Finset (GoldfishVote V)) (v : V),
      M.votes_by votes v = {vote ∈ votes | vote.val_index = v}
  /-- The definition of the reader `equivocates`.

      Read aloud: `v` equivocates in `votes` when `votes` holds at least two votes of `v`. -/
  equivocates_eq : ∀ (votes : Finset (GoldfishVote V)) (v : V),
      M.equivocates votes v = decide (2 ≤ (M.votes_by votes v).card)
  /-- The definition of the reader `participates`.

      Read aloud: `v` has a vote in `votes` when `votes` holds at least one vote of `v`. -/
  participates_eq : ∀ (votes : Finset (GoldfishVote V)) (v : V),
      M.participates votes v = decide (0 < (M.votes_by votes v).card)
  /-- The definition of the reader `no_second_vote_in`.

      Read aloud: `late` holds no second vote of `vote`'s validator when every vote of `late` is
      `vote` itself or a vote of another validator. -/
  no_second_vote_in_eq : ∀ (late : Finset (GoldfishVote V)) (vote : GoldfishVote V),
      M.no_second_vote_in late vote =
        decide (∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index)
  /-- The definition of the reader `equivocators`.

      Read aloud: the equivocators of `votes` are the validators that equivocate in `votes`. -/
  equivocators_eq : ∀ (votes : Finset (GoldfishVote V)),
      M.equivocators votes = {v ∈ (Finset.univ : Finset V) | M.equivocates votes v = true}
  /-- The definition of the reader `participants`.

      Read aloud: the participants of `votes` are the validators with a vote in `votes`. -/
  participants_eq : ∀ (votes : Finset (GoldfishVote V)),
      M.participants votes = {v ∈ (Finset.univ : Finset V) | M.participates votes v = true}
  /-- The definition of the reader `voters_count`.

      Read aloud: the voter count of `votes` is the number of participants of `votes`. -/
  voters_count_eq : ∀ (votes : Finset (GoldfishVote V)),
      M.voters_count votes = (M.participants votes).card
  /-- The definition of the reader `viable_tree`.

      Read aloud: the viable tree of `tree` holds the blocks of `tree` that are the fgroot
      `Φ.fc_root` or a descendant of it, and are a viable head of `Φ` in `tree` or an ancestor of
      one. -/
  viable_tree_eq : ∀ (Φ : Frame V) (tree : Finset (Block V)),
      M.viable_tree Φ tree =
        {B ∈ tree | Φ.fc_root.ancestorEq B && ∃ W ∈ tree ∩ Φ.viable_heads, B.ancestorEq W}
  /-- The definition of the reader `get_anchor`.

      Read aloud: the anchor of `n` at `t` is the deepest block of the viable tree of the tree of
      `M.fg_to_ac n` that is locked at `t` in `n`, when there is one, and the fgroot of
      `M.fg_to_ac n` otherwise. -/
  get_anchor_eq : ∀ [RootOrder] (n : M.N) (t : Time),
      M.get_anchor n t =
        if h : Block.deepest? {B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree |
            M.is_locked n t B = true} ≠ none
        then (Block.deepest? {B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree |
            M.is_locked n t B = true}).value h
        else (M.fg_to_ac n).fc_root
  /-- The definition of the reader `live_entries`.

      Read aloud: the live lock entries of `n` at `t` are its lock entries live at `t`. -/
  live_entries_eq : ∀ (n : M.N) (t : Time),
      M.live_entries n t = {e ∈ n.lockEntries | M.is_live n t e = true}
  /-- What the reader `saved_extends` answers, by the cases of the saved confirmation.

      Read aloud: slot `s''`'s saved confirmation in `n` extends `B` when there is one, it is in
      the tree of `M.fg_to_ac n`, and it is `B` or a descendant of `B`. -/
  saved_extends_eq : ∀ (n : M.N) (s'' : Slot) (B : Block V),
      M.saved_extends n s'' B =
        match n.savedConfirmation s'' with
        | none => false
        | some C => decide (C ∈ (M.fg_to_ac n).tree) && B.ancestorEq C
  /-- The definition of the reader `slow_test`.

      Read aloud: `B` passes `n`'s slow test of slot `s'` when `s'` is at least `C.k − 1` and the
      saved confirmation of each of the `C.k − 1` slots before `s'` extends `B`. -/
  slow_test_eq : ∀ (C : Config) (n : M.N) (s' : Slot) (B : Block V),
      M.slow_test C n s' B =
        decide (C.k - 1 ≤ s' ∧ ∀ s'' ∈ M.slots_before s' C.k, M.saved_extends n s'' B = true)
  /-- What the reader `ac_confirmed` answers.

      Read aloud: the confirmed tip of `n` is `n.latestConfirmed` when it is in the tree of
      `M.fg_to_ac n`, and the finalized block of `M.fg_to_ac n` otherwise. -/
  ac_confirmed_eq : ∀ (n : M.N),
      M.ac_confirmed n =
        if n.latestConfirmed ∈ (M.fg_to_ac n).tree then n.latestConfirmed else (M.fg_to_ac n).F
  /-- What the reader `awake_since` answers, by the cases of `n.awakeSince`.

      Read aloud: `n` has been awake since `t₀` when its wake time is set and at most `t₀`. -/
  awake_since_eq : ∀ (n : M.N) (t₀ : Time),
      M.awake_since n t₀ =
        match n.awakeSince with
        | none => false
        | some τ => decide (τ ≤ t₀)
  /-- What the reader `attestation_well_formed` answers.

      Read aloud: `a` is well formed exactly when its height is at least `1` and its finality
      pair, if any, is at a smaller height. -/
  attestation_well_formed_iff : ∀ (a : Attestation V),
      M.attestation_well_formed a = true ↔
        1 ≤ a.h ∧ ∀ p : FinalityPair, a.finality_pair = some p → p.hf < a.h
  /-- What the reader `block_well_formed` answers.

      Read aloud: `B` is well formed exactly when every attestation it includes is well formed,
      its Goldfish votes are well placed, and its root is the digest of its content. -/
  block_well_formed_iff : ∀ (P : Provisional V) (X : External V) (B : Block V),
      M.block_well_formed P X B = true ↔
        ((∀ a ∈ B.attestations, M.attestation_well_formed a = true) ∧
          M.ac_valid_payload P B = true) ∧
          B.root = X.digest B.parent.root B.slot B.attestations B.votes B.support_votes
  /-- The definition of the reader `present`.

      Read aloud: the values present in `S` are the values held by its members that are not
      none. -/
  present_eq : ∀ {α : Type} [DecidableEq α] (S : Finset (Option α)),
      M.present S = S.biUnion Option.toFinset
  /-- What the reader `advance` answers, by the cases of the confirmation `C?`.

      Read aloud: with no confirmation the confirmed tip `old` stays; with a confirmation `C`, it
      stays when it is in `Φ.tree` and `C` is `old` or an ancestor of `old`, and becomes `C`
      otherwise. -/
  advance_eq : ∀ (Φ : Frame V) (old : Block V) (C? : Option (Block V)),
      M.advance Φ old C? =
        match C? with
        | none => old
        | some C => if old ∈ Φ.tree ∧ C.ancestorEq old = true then old else C
  /-- The definition of the reader `slots_before`.

      Read aloud: the `k − 1` slots before `s'` are `s' + 1 − k + i` for `i` from `0` to
      `k − 2`. -/
  slots_before_eq : ∀ (s' : Slot) (k : ℕ),
      M.slots_before s' k = {s' + 1 - k + i | i ∈ Finset.range (k - 1)}

end GoldilocksCorrectness.Record
