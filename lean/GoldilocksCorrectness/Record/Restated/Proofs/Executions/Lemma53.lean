module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateStatementsFGState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReadersChainState
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma24

@[expose] public section

/-!
# Lemma53, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma53.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 53, the next honest proposal carries the
certificate. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_node)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_node_iff
  ancestorEq_genesis_iff state_transition_cases)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The certificate with votes already counted -/

/-! ## The votes counted along a chain -/

/-! ## Lemma 53 -/

variable [RootOrder]

/-- **Lemma 53, the next honest proposal carries the certificate.** The proof; the audited
statement is in `Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot of the proposal;
- `q`: the proposer; `B'`: the block; `H'`: its parent; `Q`: the quorum.

Read aloud: the block `B'` the honest proposer `q` proposes at the start of slot `s''` has a
chain-state height one more than its parent's, or the same height with every member of `Q` in its
progress, when every member of the quorum `Q` has an attestation at the parent's height in `q`'s
pool; and the height is one more, justifying the parent's target, when those attestations are not
timeouts. -/
theorem lem53_next_honest_proposal_carries_certificate (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s'' : ℕ) (q : V) (B' H' : Block V) (Q : Finset V)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParent : B'.parent = H')
    (hQ : quorum V ≤ Q.card)
    (hPool : ∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C s'')).attestationsHeld,
      a.val_index = u ∧ a.h = (M.chainStateOf S.C H').h ∧ a.T = (M.chainStateOf S.C H').T_h.root) :
    ((M.chainStateOf S.C B').h = (M.chainStateOf S.C H').h + 1 ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C H').h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C H').T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C s'')).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C H').h ∧
        a.T = (M.chainStateOf S.C H').T_h.root ∧ a.τ = false) →
      (M.chainStateOf S.C B').h = (M.chainStateOf S.C H').h + 1 ∧
        (M.chainStateOf S.C B').J = (M.chainStateOf S.C H').T_h) := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  -- the slot is not `0`: a tick that sends a block is at a time of a positive slot (Lemma 19
  -- over the record, `0 < C.slot t`), from the tick's input, which satisfies the node invariant
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, s'' = s + 1 := by
    rcases s'' with _ | s
    · exfalso
      obtain ⟨-, n₀, sent₀, hrun₀, hB₀⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
      have hti₀ : x.tickInput q (M.slotStart S.C 0) = x.st i q := by
        unfold Trace.tickInput
        rw [(tickStep_eq_of_lbl M) x E hl]
      have hInv₀ : M.nodeInv S.C S.P S.X (x.tickInput q (M.slotStart S.C 0)) := by
        rw [hti₀]
        exact (lem11_node_invariant M F S A x R E i q (E.not_mem_corrupted_of_tick hl)).1
      have hpos := ((GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₀ _
        sent₀ B' hrun₀ hInv₀ hB₀).1
      have hΔ := one_le_Δ S
      have h00 : M.slotStart S.C 0 = 0 := by rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_zero]
      have h01 : M.slotStart S.C (0 + 1) = 4 * Δ S := by rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.zero_add, Nat.mul_one]
      have hslot₀ : S.C.slot ((M.slotStart S.C 0 : ℕ) : Int) = 0 := by
        rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
          ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
        exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
          (by omega)
      rw [hslot₀] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact ⟨s, rfl⟩
  obtain ⟨-, -, -, hEnd⟩ := (proposal_parent_walk_end M F U) S A x R E s i B' q hl hsent
  rw [hParent] at hEnd
  -- the proposal's attestations are the pool's, on the parent `H'`
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
  -- the slot of `t₁`, read by the spec's clock (the model's slot of a natural-number time is the
  -- spec's, `U`)
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
      (by omega)
  -- `q`'s run and proposal, at the step `i` (Lemma 19 over the record, the field `tick_proposal` of
  -- `F.tk3`, from the tick's input state, which satisfies the node invariant and is `q`'s state
  -- before the start of slot `s + 1`, by its wake time)
  obtain ⟨hqact, n₁', sent₁, hrun₁, hB₁⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hti : x.tickInput q (M.slotStart S.C (s + 1)) = x.st i q := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput q (M.slotStart S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x R E i q (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨-, -, -, ⟨τ, hτ, -⟩, Hp, votes_pl, support_pl, -, -, -, hBdef⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem19_tick_proposes F) S.C S.P S.X _ n₁' _ sent₁ B'
      hrun₁ hInvT hB₁
  rw [hslot₁] at hBdef
  have hHp : Hp = H' := by rw [← hParent, hBdef]; rfl
  subst hHp
  have hatts : B'.attestations =
      M.proposal_attestations (x.tickInput q (M.slotStart S.C (s + 1))) Hp := by
    rw [hBdef]; rfl
  have hBne : B' ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  -- the node invariant of `q` before the start of slot `s + 1`
  have hinv := hInvT
  have hHT : Hp ∈ (x.tickInput q (M.slotStart S.C (s + 1))).tree :=
    (GoldilocksCorrectness.Record.Proofs.Routines.walk_end_mem_T M F) S.C S.P S.X _ hinv _ Hp hEnd
      (F.nd.nodeInv_finalized_mem_tree hinv)
      ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A
        x R E _ q).2.2.1
  have hValidChain : ∀ Y : Block V, Y.AncestorEq Hp → Y ≠ Block.genesis →
      ∀ a' ∈ Y.attestations, M.valid_attestation (M.chainStateOf S.C Y.parent) a' = true := by
    intro Y hY hne a' ha'
    have hYT :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ q Hp Y hHT hY
    exact F.nd.nodeInv_attestationsValid hinv Y hYT hne a' ha'
  -- every pool attestation at `H'`'s height naming its `T_h` is counted on `H'`'s chain, or
  -- included in `B'`
  have hcount : ∀ a ∈ (x.tickInput q (M.slotStart S.C (s + 1))).attestationsHeld,
      a.h = (M.chainStateOf S.C Hp).h → a.T = (M.chainStateOf S.C Hp).T_h.root →
      (a.val_index ∈ (M.chainStateOf S.C Hp).progress ∧
        (a.τ = false → a.val_index ∈ (M.chainStateOf S.C Hp).target_participation)) ∨
      a ∈ B'.attestations := by
    intro a ha hh hT
    cases hon : M.on_chain a Hp
    · right
      rw [hatts]
      exact (GoldilocksCorrectness.Record.Statements.Routines.lem52_pool_attestation_included M F) S.C S.P S.X _
        hinv Hp hHT a ha ((GoldilocksCorrectness.Record.Proofs.Routines.valid_attestation_of_height M F) _ a
          hh hT) hon
    · exact Or.inl ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_counted M F) S.C Hp a hon
        hValidChain hh)
  -- the certificate (Lemma 51 with votes already counted; the quorum at `B'` is `quorum V`, the
  -- validators being fixed)
  have hpar : B'.parent = Hp := hParent
  obtain ⟨h1, h2⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.quorum_certificate_with_counted M F) S.C
    B' hBne Q
    (by rw [show M.quorumAt B' = quorum V from GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched B']
        exact hQ)
    (fun u hu => by
      obtain ⟨a, ha, hau, hh, hT⟩ := hPool u hu
      rw [hpar]
      rcases hcount a ha hh hT with ⟨hp, -⟩ | hin
      · exact Or.inl (hau ▸ hp)
      · exact Or.inr ⟨a, hin, hau, hh, hT⟩)
  rw [hpar] at h1 h2
  refine ⟨h1, fun hT => ?_⟩
  obtain ⟨k1, k2, -⟩ := h2 (fun u hu => by
    obtain ⟨a, ha, hau, hh, hT', hτ⟩ := hT u hu
    rcases hcount a ha hh hT' with ⟨-, hp⟩ | hin
    · exact Or.inl (hau ▸ hp hτ)
    · exact Or.inr ⟨a, hin, hau, hh, hT', hτ⟩)
  exact ⟨k1, k2⟩

end GoldilocksCorrectness.Record.Proofs.Executions

