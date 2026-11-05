module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma94Pair
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FinalityPair
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.Lemma94Pair
public import GoldilocksCorrectness.Proofs.Routines.FinalityPair
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma95Pair, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma95Pair.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 95, two consecutive honest round
opening slots give the height step and the finalization, and its kit on the execution, namely an
honest attestation reaching an awake honest validator's pool and the attestations of an honest
proposal. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ proposalWindowStart_add_Δ_F_le slotStart_eq slotStart_mono slot_after_healed_round
  slot_eq_of_mem supportCutoff_eq supportCutoff_succ_add_Δ_F_le_slotStart voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_node chainStateOf_pending_last)

open GoldilocksCorrectness.Proofs.Routines (pending_pair_along_chain)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_node_iff
  ancestorEq_genesis_iff process_attestations_eq process_attestations_eq_foldl
  foldl_finality_participation process_height_events_cases state_transition_eq advance_height_eq
  value_eq_of_eq_some)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The pending justifications along a chain -/

/-! ## The execution: delivery to the pool, and the proposal's attestations -/

/-- **Kit fact, the attestations of an honest proposal.** When `q` put the block `B'` on the wire
at its tick at the start of slot `s''`, `B'`'s attestations are those of `q`'s pool before that
start that are valid against `B'`'s parent's chain state and not on its chain
(`proposal_attestations`), the parent is in `q`'s tree then, and `q`'s chain state of the parent is
the parent's own.

Why: the first steps of the proof of Lemma 53 (`Proofs/Executions/Lemma53.lean`): the tick ran the
proposal (Lemma 19), whose parent is the end of the walk, in the tree.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot; `q`: the proposer;
  `B'`: the block.

Read aloud: the attestations of a block an honest proposer sent at the start of slot `s''` are those
of its pool on the block's parent, the parent is in its tree then, and its chain state of the parent
is the parent's own. -/
theorem proposal_attestations_of_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s'' : ℕ) (q : V) (B' : Block V)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    B'.attestations = M.proposal_attestations (x.tickInput q (M.slotStart S.C s'')) B'.parent ∧
      B'.parent ∈ (x.tickInput q (M.slotStart S.C s'')).tree ∧
      M.chainStateOf S.C B'.parent = M.chainStateOf S.C B'.parent := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  have hqi : q ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, s'' = s + 1 := by
    rcases s'' with _ | s
    · exfalso
      -- a tick to the reading `0` proposes nothing: Lemma 19 puts a proposal in a slot `> 0`
      have hTI0 : x.tickInput q (M.slotStart S.C 0) = x.st i q := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M x E) hl]
      obtain ⟨-, n₀, sent₀, hrun₀, hB₀⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
      have hInv0 : M.nodeInv S.C S.P S.X (x.tickInput q (M.slotStart S.C 0)) := by
        rw [hTI0]
        exact (lem11_node_invariant M F S A x R E i q hqi).1
      have hpos := (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₀ _ sent₀ B'
        hrun₀ hInv0 hB₀
      have h0 : M.slotStart S.C 0 = 0 := by rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_zero]
      have hΔ := one_le_Δ S
      have h1 : M.slotStart S.C 1 = 4 * Δ S := by
        rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_one]
      have hsl0 : S.C.slot ((M.slotStart S.C 0 : ℕ) : Int) = 0 := by
        rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
          ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
          (by rw [h1, h0]; omega)
      have := hpos.1
      rw [hsl0] at this
      exact absurd this (lt_irrefl 0)
    · exact ⟨s, rfl⟩
  obtain ⟨-, -, -, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s i B' q hl hsent
  have hΔ := one_le_Δ S
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  -- the slot of the start of slot `s + 1`, read by the spec's clock (the model's slot of a
  -- natural-number time is the spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
      (by omega)
  -- `q`'s run and proposal, at the step `i` (Lemma 19 over the record, from the tick's input state,
  -- which satisfies the node invariant and is `q`'s state before the start of slot `s + 1`, by its
  -- wake time; as the twin of Lemma 53's proof)
  have hSBTI : x.tickInput q (M.slotStart S.C (s + 1)) = x.st i q := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M x E) hl]
  obtain ⟨hpA, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput q (M.slotStart S.C (s + 1))) := by
    rw [hSBTI]
    exact (lem11_node_invariant M F S A x R E i q hqi).1
  obtain ⟨-, -, -, ⟨τ, hτ, -⟩, Hp, votes_pl, support_pl, -, -, -, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B'
      hrun₁ hInvT hB₁
  rw [hslot₁] at hBdef
  have hHp : B'.parent = Hp := by rw [hBdef]; rfl
  rw [hHp] at hEnd ⊢
  have hatts : B'.attestations =
      M.proposal_attestations (x.tickInput q (M.slotStart S.C (s + 1))) Hp := by
    rw [hBdef]; rfl
  have hHT : Hp ∈ (x.tickInput q (M.slotStart S.C (s + 1))).tree := by
    rw [hSBTI] at hEnd ⊢
    have hinv := (lem11_node_invariant M F S A x R E i q hqi).1
    exact (GoldilocksCorrectness.Record.Proofs.Routines.walk_end_mem_T M F) S.C S.P S.X _ hinv _ Hp hEnd
      (F.nd.nodeInv_finalized_mem_tree hinv)
      ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A
        x R E i q).2.2.1
  exact ⟨hatts, hHT, rfl⟩

/-! ## Lemma 95 -/

/-- **Kit theorem, a pending justification along a chain.** When `h_F(B) < h_j(B)`, `B` is `X` or
an ancestor of `X`, and every block from `B` to `X` has a justification height at most `h(B)`:
the chain state of `X` finalizes at a height at least `h_j(B)`, or keeps pending a pair `e₀` at
the height `h_j(B)` naming `J(B)`, with at most one pending pair after it, and counts at `h_j(B)`
the validator of every attestation with the finality pair `(h_j(B), J(B))` on `X`'s chain and not
on `B`'s.

Why: by induction on `X`. At `B`, the pair is the last pending one (the facts'
`chainStateOf_pending_last`); each transition after `B` keeps it, or finalizes at least its height
(`pending_pair_step`), the height staying at least `h(B)` (Lemma 47 (d)); a block's attestations
are on its chain, the others on its parent's; and the finalization height only rises.

It is the landed `GoldilocksCorrectness.Proofs.Routines.pending_pair_along_chain` over the record,
which has no record twin: the record names the pending pair by its readers (`e₀.j`, `e₀.T`), as the
facts' `chainStateOf_pending_last` does.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the first block; `X`: its descendant.

Read aloud: along a chain from `B` whose justifications are at heights at most `h(B)`, `B`'s
unfinalized justification stays pending with at most one pair after it, collecting the
attestations that carry it, unless it is finalized on the way. -/
theorem pending_pair_kept_along_chain (C : Config) (B X : Block V) (hBX : B.AncestorEq X)
    (hlt : (M.chainStateOf C B).h_F < (M.chainStateOf C B).h_j)
    (hbound : ∀ Y : Block V, B.AncestorEq Y → Y.AncestorEq X →
      (M.chainStateOf C Y).h_j ≤ (M.chainStateOf C B).h) :
    (M.chainStateOf C B).h_j ≤ (M.chainStateOf C X).h_F ∨
      ∃ e₀ : M.PP, e₀.j = (M.chainStateOf C B).h_j ∧ e₀.T = (M.chainStateOf C B).J ∧
        (∃ l₁ l₂ : List M.PP, (M.chainStateOf C X).pending_finality = l₁ ++ e₀ :: l₂ ∧
          (l₂ = [] ∨ (l₂.length = 1 ∧ (M.chainStateOf C B).h + 1 ≤ (M.chainStateOf C X).h))) ∧
        ∀ a : Attestation V,
          a.finality_pair =
            some (FinalityPair.mk (M.chainStateOf C B).h_j (M.chainStateOf C B).J.root) →
          M.on_chain a X = true →
          M.on_chain a B = true ∨
            a.val_index ∈ (M.chainStateOf C X).finality_participation (M.chainStateOf C B).h_j := by
  -- the pair at `B`: the last pending one
  obtain ⟨l, e₀, hl, hej, heT⟩ := F.cs.chainStateOf_pending_last C B hlt
  suffices h : (M.chainStateOf C B).h_j ≤ (M.chainStateOf C X).h_F ∨
      ((∃ l₁ l₂ : List M.PP, (M.chainStateOf C X).pending_finality = l₁ ++ e₀ :: l₂ ∧
          (l₂ = [] ∨ (l₂.length = 1 ∧ (M.chainStateOf C B).h + 1 ≤ (M.chainStateOf C X).h))) ∧
        ∀ a : Attestation V,
          a.finality_pair =
            some (FinalityPair.mk (M.chainStateOf C B).h_j (M.chainStateOf C B).J.root) →
          M.on_chain a X = true →
          M.on_chain a B = true ∨
            a.val_index ∈ (M.chainStateOf C X).finality_participation (M.chainStateOf C B).h_j) by
    rcases h with h | ⟨hshape, hpart⟩
    · exact Or.inl h
    · exact Or.inr ⟨e₀, hej, heT, hshape, hpart⟩
  -- the case `X = B`
  have hbase : (M.chainStateOf C B).h_j ≤ (M.chainStateOf C B).h_F ∨
      ((∃ l₁ l₂ : List M.PP, (M.chainStateOf C B).pending_finality = l₁ ++ e₀ :: l₂ ∧
          (l₂ = [] ∨ (l₂.length = 1 ∧ (M.chainStateOf C B).h + 1 ≤ (M.chainStateOf C B).h))) ∧
        ∀ a : Attestation V,
          a.finality_pair =
            some (FinalityPair.mk (M.chainStateOf C B).h_j (M.chainStateOf C B).J.root) →
          M.on_chain a B = true →
          M.on_chain a B = true ∨
            a.val_index ∈ (M.chainStateOf C B).finality_participation (M.chainStateOf C B).h_j) :=
    Or.inr ⟨⟨l, [], hl, Or.inl rfl⟩, fun a _ ha => Or.inl ha⟩
  induction X with
  | genesis =>
      rw [(ancestorEq_genesis_iff B).1 hBX] at hbase ⊢
      exact hbase
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hBX with heq | hBp
      · rw [← heq]; exact hbase
      have hpX : p.AncestorEq (Block.node p s r votes support ats v) :=
        (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl p))
      have hmonoF := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_h_j_h_F_mono M F) C p _ hpX).2
      rcases ih hBp (fun Y h1 h2 => hbound Y h1 (ancestorEq_trans h2 hpX)) with hle | ⟨hshape, hpart⟩
      · exact Or.inl (le_trans hle hmonoF)
      have hBh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) C B B).1
      have hhp := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) C B p).2.2.2.1 hBp
      have hJX := hbound _ hBX (ancestorEq_refl _)
      rcases (GoldilocksCorrectness.Record.Proofs.Routines.pending_pair_step M F) C
          (Block.node p s r votes support ats v) (fun h => by cases h) e₀ (M.chainStateOf C B).h hshape
          (by rw [hej]; exact hBh.2.1) hhp hJX with hle | ⟨hshape', hmono, hadd⟩
      · exact Or.inl (by rw [← hej]; exact hle)
      refine Or.inr ⟨hshape', fun a hp hon => ?_⟩
      rw [F.rd.on_chain_eq, F.rd.attestations_on_chain_node, decide_eq_true_eq, List.mem_append] at hon
      rcases hon with hin | hin
      · exact Or.inr (by rw [← hej]; exact hadd a hin (by rw [hej, heT]; exact hp))
      · rcases hpart a hp (by rw [F.rd.on_chain_eq, decide_eq_true_eq]; exact hin) with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [← hej] at h ⊢; exact hmono _ h)

/-- **Lemma 95, two consecutive honest round opening slots: the height step and the
finalization.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals.

Read aloud: when no honest validator has attested above `B`'s justification height before round
`r`'s action time, and that height is greater than the threshold, the next honest round opening slot
extends the previous one's proposal, raises the height, and finalizes the previous proposal's
justification, provided no member of round `r` already holds, when it attests, a block including one of the
round's own attestations. -/
theorem lem95_consecutive_openings_step (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hAfter : x.time i₂ < M.slotStart S.C (r * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start, or held by it before its
    -- proposal window starts
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) (S.P.proposer ((r + 1) * S.C.R))).attestationsHeld)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hOldJ : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (r * S.C.R + 1)) (M.supportCutoff S.C (r * S.C.R + 1))
      (M.chainStateOf S.C B).h_j)
    -- no block an honest active member of the round holds when it ticks to the round's action time includes an
    -- attestation put on the wire at a tick to that action time
    (hTickInputs : ∀ v ∈ honestActiveAt M S A x (r * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    (hHJ : H < (M.chainStateOf S.C B).h_j) :
    B.AncestorEq B' ∧ (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
      (M.chainStateOf S.C B).h_j ≤ (M.chainStateOf S.C B').h_F := by
  obtain ⟨-, -, hBP, hPB', -, hB'T, hstep, -⟩ := (consecutive_openings_step_kit M F U Fx) S A x R GST s₀
    anchor i₂ H r B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsK hParent hAdvQ
    hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hCachesK hParam hAfter hOpener
    hOpener' hQuorum hDel hPropose hPropose' hNoCol hNoCol' hHold hHold' hHoldP hHoldP'
  have hBB' : B.AncestorEq B' := ancestorEq_trans hBP hPB'
  refine ⟨hBB', hstep, ?_⟩
  by_cases hFj : (M.chainStateOf S.C B).h_j ≤ (M.chainStateOf S.C B).h_F
  · exact le_trans hFj ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_h_j_h_F_mono M F) S.C B B' hBB').2
  have hFj' : (M.chainStateOf S.C B).h_F < (M.chainStateOf S.C B).h_j := Nat.lt_of_not_le hFj
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hRR : (2 : ℝ) ≤ (S.C.R : ℝ) := by exact_mod_cast hR
  have hΔRR : 2 * (Δ S : ℝ) ≤ (Δ S : ℝ) * (S.C.R : ℝ) := by nlinarith
  have hΔF0 : (0 : ℝ) ≤ (Δ_F S : ℝ) := by positivity
  have hss' : (r + 1) * S.C.R = r * S.C.R + S.C.R := by rw [Nat.add_mul, Nat.one_mul]
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ (r * S.C.R) (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  -- the two slots `s = q + 2` and `s' = q' + 2`, with `q' = q + R`
  generalize hsd : r * S.C.R = s at *
  generalize hs'd : (r + 1) * S.C.R = s' at *
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', s' = q' + 2 := ⟨s' - 2, by omega⟩
  have hq'q : ((q' : ℕ) : ℝ) = (q : ℝ) + (S.C.R : ℝ) := by exact_mod_cast (show q' = q + S.C.R by omega)
  have hsub' : q' + 2 - 1 = q' + 1 := by omega
  rw [hsub'] at hHold'
  -- the times of the slots
  have hsR : ∀ σ : ℕ, ((M.slotStart S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) := fun σ => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ]; push_cast; ring
  have hvR : ∀ σ : ℕ, ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + Δ S := fun σ => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ,
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ]; push_cast; ring
  have hcR : ∀ σ : ℕ, ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 2 * Δ S := fun σ => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ,
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ,
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ]; push_cast; ring
  -- the updaters of `s` tick to the support cutoff of `s + 1`, a clock value at most the vote time of `s'`
  have hcle : M.supportCutoff S.C (q + 2 + 1) ≤ M.voteTime S.C (q' + 2) := by
    have e1 := hcR (q + 2 + 1)
    have e2 := hvR (q' + 2)
    push_cast at e1 e2
    have : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) ≤ ((M.voteTime S.C (q' + 2) : ℕ) : ℝ) := by
      rw [e1, e2, hq'q]; nlinarith
    exact_mod_cast this
  -- a tick to a clock value at most the vote time of `s'` is at a real time at most the support cutoff of `s' + 1`
  have hkV : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q' + 2) →
      x.time k ≤ ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
    intro k u c hk hc
    have h1 := (E.tick_active k u c hk).2.2
    have hcR' : (c : ℝ) ≤ ((M.voteTime S.C (q' + 2) : ℕ) : ℝ) := by exact_mod_cast hc
    have e1 := hvR (q' + 2)
    have e2 := hcR (q' + 2 + 1)
    push_cast at e1 e2
    linarith
  -- the rows at round `r`, at each updater's own tick and as real times up to the support cutoff of `s + 1`
  obtain ⟨hRootsU, hAdvQU, hCachesU⟩ := (updater_rows_of_tick_rows M F) S A x E s₀ H i₂ (q + 2) _ _ hcle hRootsK
    hCachesK hAdvQ hkV
  have hcvR : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) ≤ ((M.voteTime S.C (q' + 2) : ℕ) : ℝ) := by
    exact_mod_cast hcle
  have hccR : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
    exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show q + 2 + 1 ≤ q' + 2 + 1 by omega)
  have hRootsS := (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hcvR hRoots
  have hCachesS : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (q + 2 + 1) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w) :=
    fun j w h₁ h₂ h₃ => hCaches j w h₁ (le_trans h₂ hcvR) h₃
  have hSleepS := hSleepK.mono M ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show q + 2 + 1 ≤ q' + 2 by omega))
  have hChainS : ConfirmationsChainBefore M S A x s₀ (q + 2) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hChainS1 : ConfirmationsChainBefore M S A x s₀ (q + 2 + 1) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hInvS := fun s'' (h₁ : s₀ < s'') (h₂ : s'' ≤ q + 2) => hInv s'' h₁ (by omega)
  have hLocksS := fun s'' (h₁ : s₀ < s'') (h₂ : s'' ≤ q + 2) => hLocks s'' h₁ (by omega)
  -- Lemma 107 at `r`: every honest attestation before the support cutoff of `s' + 1` is at most `h(B)`
  have h107 := (lem107_honest_attestations_at_most_opening_height M F U Fx) S A x R GST s₀ anchor i₂ H r (q + 2) B
    E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepS hAnchor hGST ht₀ hChainS hInvS hLocksS hLocks₀
    hOld hCachesU hsd.symm hAfter hOpener hPropose hNoCol hHold hHoldP
  rw [hs'd] at h107
  -- the next opener's tick to its slot's vote time, where it holds `B'`
  have hp'H := (opener_mem_honestActiveAt M F U) S A R E q' hOpener'
  obtain ⟨kv, hkv, -⟩ := Activity.mem_activeThroughoutToTick.1
    ((reader_vote_of_honestActiveAt M F U) R E hSkew hp'H)
  have hkvs : x.tickStep (S.P.proposer (q' + 2)) (M.voteTime S.C (q' + 2)) = kv := (tickStep_eq_of_lbl M) x E hkv
  have hB'T' : B' ∈ (x.st kv (S.P.proposer (q' + 2))).tree := by
    have h := hB'T
    unfold Trace.tickInput at h
    rw [hkvs] at h
    exact h
  have hkvA : x.time kv + ΔClockAhead < ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
    have h1 := (E.tick_active kv _ _ hkv).2.2
    have e1 := hvR (q' + 2)
    have e2 := hcR (q' + 2 + 1)
    push_cast at e1 e2
    linarith
  have hkvlt : x.time kv < ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by linarith
  -- every block from `B` to `B'`'s parent has a justification height at most `h(B)`
  have hbound : ∀ Y : Block V, B.AncestorEq Y → Y.AncestorEq B'.parent →
      (M.chainStateOf S.C Y).h_j ≤ (M.chainStateOf S.C B).h := by
    intro Y _ hYP
    have hYT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ _ B' Y
      hB'T' (ancestorEq_trans hYP hPB')
    rcases Nat.eq_zero_or_pos (M.chainStateOf S.C Y).h_j with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    have hcert := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Y).1 h0).1
    exact (justification_cert_height_le M F Fx) S A x R E _ _ _ _ Y _ _ hAdvQ h107 hkvlt hkvA hYT hcert
  rcases (pending_pair_kept_along_chain M F) S.C B B'.parent hBP hFj' hbound with hle |
      ⟨e₀, hej, heT, ⟨l₁, l₂, hpend, -⟩, hpart⟩
  · exact le_trans hle ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_h_j_h_F_mono M F) S.C _ _ hPB').2
  have he₀P : e₀ ∈ (M.chainStateOf S.C B'.parent).pending_finality := by
    rw [hpend]; simp
  -- the members' justified heights before the proposal window of `s'`, and the window before the next opener's tick
  obtain ⟨ip', hl', hsent'⟩ := hPropose'
  have hpw := (GoldilocksCorrectness.Record.Proofs.Routines.proposalWindowStart_add_Δ_F_le M.toSlotLayout F.sched U) S
    (show S.C.R ≤ q' + 2 by omega) hParam
  have hpwR : ((M.proposalWindowStart S.C (q' + 2) : ℕ) : ℝ) + Δ_F S ≤ ((M.slotStart S.C (q' + 2) : ℕ) : ℝ) := by
    exact_mod_cast hpw
  have hstc : ((M.slotStart S.C (q' + 2) : ℕ) : ℝ) < ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
    rw [hsR, hcR]; push_cast; nlinarith
  have hpwA : ((M.proposalWindowStart S.C (q' + 2) : ℕ) : ℝ) + ΔClockAhead <
      ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
    linarith
  have hpwc : M.proposalWindowStart S.C (q' + 2) < M.supportCutoff S.C (q' + 2 + 1) := by
    have : ((M.proposalWindowStart S.C (q' + 2) : ℕ) : ℝ) < ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
      linarith
    exact_mod_cast this
  have hselq : ∀ u : V,
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C (q' + 2)) u) ≤ (M.chainStateOf S.C B).h :=
    fun u => (justifiedHeight_le_of_oldAttestations M F Fx) S A x R E _ _ _ u hAdvQ h107 hpwc hpwA
  have hle : x.stepBefore (M.proposalWindowStart S.C (q' + 2)) ≤
      x.tickStep (S.P.proposer (q' + 2)) (M.slotStart S.C (q' + 2)) := by
    rw [(tickStep_eq_of_lbl M) x E hl']
    exact (stepBefore_le_of_le_time_st M F) R E (by have := (E.tick_active ip' _ _ hl').2.1; linarith)
  obtain ⟨hatts, hPT, -⟩ := (proposal_attestations_of_tick M F U) S A x R E (q' + 2) (S.P.proposer (q' + 2)) B'
    ⟨ip', hl', hsent'⟩
  have hIn : M.nodeInv S.C S.P S.X (x.tickInput (S.P.proposer (q' + 2)) (M.slotStart S.C (q' + 2))) := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl']
    exact (lem11_node_invariant M F S A x R E ip' _ (E.not_mem_corrupted_of_tick hl')).1
  -- Lemma 93 at `B'`
  refine (GoldilocksCorrectness.Record.Statements.Routines.lem93_block_finalizes_pending M F) S.C B' B'.parent
    (M.chainStateOf S.C B).h_j (M.chainStateOf S.C B).J (honestActiveAt M S A x (q + 2)) rfl ⟨e₀, he₀P, hej, heT⟩
    (by rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched B']; exact hQuorum)
    (fun v hv => ?_)
  -- the member's attestation of Lemma 94, carrying the pair
  obtain ⟨i, a, hl, hsent, hav, hah, haT, -, hpair⟩ := (lem94_round_attesters_after_healing M F U Fx) S A x R
    GST s₀ anchor i₂ H r (q + 2) B v E hNet hSkew hRedeliver Sy hΔs hRootsS hRootsU hParent (hAdvQ.mono hccR) hAdvQU
    hSleepS hAnchor hGST ht₀ hChainS1 hInvS hLocksS hLocks₀ hOld hCachesS hCachesU hsd.symm hAfter hOpener hPropose
    hNoCol hHold hHoldP hOldJ hHJ hTickInputs hv
  -- `v`'s tick to the support cutoff of `s + 1`
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1
    ((honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) hv)
  have hks : x.tickStep v (M.supportCutoff S.C (q + 2 + 1)) = k := (tickStep_eq_of_lbl M) x E hk
  have hTIk : ∀ Z ∈ (x.st k v).tree, ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w' : V),
      x.lbl j = Event.tick w' (M.supportCutoff S.C (q + 2 + 1)) →
      (⟨w', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j := by
    intro Z hZ
    refine hTickInputs v hv Z ?_
    unfold Trace.tickInput
    rw [hks]
    exact hZ
  rcases hpair hFj' with hp | ⟨D, hD, -, hFD⟩
  swap
  · -- a block `v` holds at its tick finalizes at a height less than `h_j(B)` (the finality certificate's honest
    -- member attested before the action time, at a height at most `h_j(B)`), against `hFD`
    exfalso
    have hD' : D ∈ (x.st k v).tree := by
      unfold Trace.tickInput at hD
      rw [hks] at hD
      exact hD
    have hF1 : 1 ≤ (M.chainStateOf S.C D).h_F := by omega_nat
    have hcert := ((((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
      hF1).2.1)
    have := (finality_cert_height_lt_at_tick M F U Fx) S A x R E hSkew r (q + 2) _ k v _ D _ _ hsd.symm hk
      (hkV k v _ hk hcle) hccR hAdvQ hOldJ hTIk hD' hcert
    omega_nat
  -- the attestation is not on `B`'s chain: `B` is in `v`'s tick input, whose blocks include no attestation of a tick
  -- to the action time (`hTickInputs`)
  have hnotB : M.on_chain a B = false := by
    by_contra hon
    have hon' : M.on_chain a B = true := by simpa using hon
    obtain ⟨-, -, -, -, -, -, -, -, hBin, -⟩ := (round_member_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H
      (q + 2) B v E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepS hAnchor hGST ht₀ hChainS hInvS hLocksS
      hLocks₀ hOld hCachesU hAfter hOpener hPropose hNoCol hHold hHoldP hv
    have hBin' : B ∈ (x.st k v).tree := by
      unfold Trace.tickInput at hBin
      rw [hks] at hBin
      exact hBin
    obtain ⟨X, hX, haX⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F) a B).1 hon'
    have hXT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k v B X
      hBin' hX
    have hik : i = k := (E.tick_unique i k v _ hl hk)
    subst hik
    exact hTIk X hXT a haX i v hl hsent
  by_cases hon : M.on_chain a B'.parent = true
  · rcases hpart a hp hon with h | h
    · rw [hnotB] at h; cases h
    · left; rw [hav] at h; exact h
  right
  -- the attestation reaches the next opener's tick input to its slot's start, by `hDel`
  have hdel := hDel v hv i _ a hl le_rfl hsent (by rw [hah]; exact hselq v)
  have hpool := (attestation_in_tickInput_of_delivery_or_held M F) S A x R E hNet hSkew hRedeliver _ _ _ hle i _ v a
    hl hsent hdel
  refine ⟨a, ?_, hav, hp⟩
  rw [hatts]
  refine (GoldilocksCorrectness.Record.Statements.Routines.lem52_pool_attestation_included M F) S.C S.P S.X _
    hIn _ hPT a hpool ?_ (by simpa using hon)
  -- valid against the parent: at its height naming its `T_h`, or through the pending pair
  have hPh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.1 hBP
  rcases Nat.lt_or_ge (M.chainStateOf S.C B).h (M.chainStateOf S.C B'.parent).h with hgt | hle'
  · refine (GoldilocksCorrectness.Record.Proofs.Routines.valid_attestation_of_pending M F) _ a _ hp ?_ ?_
      (by rw [hah]; exact hgt)
    · exact ((GoldilocksCorrectness.Record.Proofs.Routines.is_pending_iff M F) _ _).2
        ⟨e₀, he₀P, hej, by rw [heT]⟩
    · rw [hah]; exact ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B).1.2.1
  · have heq : (M.chainStateOf S.C B).h = (M.chainStateOf S.C B'.parent).h := le_antisymm hPh hle'
    have hTh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.2
      hBP heq
    exact (GoldilocksCorrectness.Record.Statements.Routines.valid_attestation_of_height M F) _ a (by rw [hah, heq])
      (by rw [haT, hTh])

end GoldilocksCorrectness.Record.Proofs.Executions

