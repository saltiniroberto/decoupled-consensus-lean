module
public import GoldilocksCorrectness.Statements.Routines.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma24
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!
# Lemma 53: the next honest proposal carries the certificate

The proof of `lem53_next_honest_proposal_carries_certificate`, stated in
`GoldilocksCorrectness/Statements/Executions/HeightAttestationStatements.lean`, and the kit facts
it needs: Lemma 51 with some of the quorum already counted in the parent's chain state
(`quorum_certificate_with_counted`), and the counting of an attestation included on a chain
(`on_chain_counted`, through `valid_attestation_cases`, `exists_of_on_chain` and
`counted_kept_of_same_height`).

The route: the block `q` proposed has the parent `H'`, the end of `q`'s walk, which is in `q`'s
tree (`walk_end_mem_T`), and includes the attestations of `q`'s pool valid against `H'`'s chain
state and not on `H'`'s chain (Lemma 19). A pool attestation at `H'`'s height naming `H'`'s `T_h`
is valid, so it is included (Lemma 52) or it is on `H'`'s chain; an attestation on the chain was
included in a block whose parent had that height (it was valid there, a node invariant), so its
validator was counted there and stays counted while the height does not move. With every member
of `Q` counted or included, the quorum is a certificate.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono chainStateOf_node
  counted_kept_of_same_height quorum_certificate_with_counted valid_attestation_cases)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree on_chain_counted)
open GoldilocksCorrectness.Statements.Routines (AttestationsValid ChainStatesComputed
  JustifiedInTree)

open GoldilocksCorrectness.Proofs.Routines (walk_end_mem_T)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_node_iff
  ancestorEq_genesis_iff state_transition_cases)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The certificate with votes already counted -/

/-! ## The votes counted along a chain -/


/-! ## Lemma 53 -/

variable [RootOrder]

/-- **Lemma 53, the next honest proposal carries the certificate.** The proof; the audited
statement is in `Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot of the proposal;
- `q`: the proposer; `B'`: the block; `H'`: its parent; `Q`: the quorum. -/
theorem lem53_next_honest_proposal_carries_certificate (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (s'' : ℕ) (q : V) (B' H' : Block V) (Q : Finset V)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParent : B'.parent = H')
    (hQ : quorum V ≤ Q.card)
    (hPool : ∀ u ∈ Q, ∃ a ∈ (stateBefore x (slotStart S s'') q).S.attestations,
      a.val_index = u ∧ a.h = (chainStateOf S.C H').h ∧ a.T = (chainStateOf S.C H').T_h.root) :
    ((chainStateOf S.C B').h = (chainStateOf S.C H').h + 1 ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C H').h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C H').T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∃ a ∈ (stateBefore x (slotStart S s'') q).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C H').h ∧
        a.T = (chainStateOf S.C H').T_h.root ∧ a.τ = false) →
      (chainStateOf S.C B').h = (chainStateOf S.C H').h + 1 ∧
        (chainStateOf S.C B').J = (chainStateOf S.C H').T_h) := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  -- the slot is not `0`: no tick is at the time `0`
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, s'' = s + 1 := by
    rcases s'' with _ | s
    · exfalso
      have h1 := (time_of_lbl_tickAllAwake x hl).1
      have h0 : slotStart S 0 = 0 := by rw [slotStart_eq, Nat.mul_zero]
      omega
    · exact ⟨s, rfl⟩
  obtain ⟨-, -, -, hEnd⟩ := proposal_parent_walk_end S Sched x s i B' q hl hsent
  rw [hParent] at hEnd
  -- the proposal's attestations are the pool's, on the parent `H'`
  have hΔ := one_le_Δ S
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  have hSp : (tickInputState x i (slotStart S (s + 1)) q).S =
      (stateBefore x (slotStart S (s + 1)) q).S := by
    rw [(tickInputState_frame x i _ q).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, -, -, -, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B'
      hrun₁ hB₁
  rw [hslot₁, hSp] at hBdef
  have hHp : Hp = H' := by rw [← hParent, hBdef]; rfl
  subst hHp
  have hatts : B'.attestations =
      proposal_attestations (stateBefore x (slotStart S (s + 1)) q).S Hp := by
    rw [hBdef]; rfl
  have hst : chainStateOf S.C B' = state_transition S.C (chainStateOf S.C Hp) B' := by
    rw [hBdef]; rfl
  -- the node invariant of `q` before the start of slot `s + 1`
  have hinv := (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) q).1
  have hCSC : ChainStatesComputed S.C (stateBefore x (slotStart S (s + 1)) q).S :=
    hinv.2.2.2.2.2.1
  have hAV : AttestationsValid (stateBefore x (slotStart S (s + 1)) q).S :=
    hinv.2.2.2.2.2.2.1
  have hHT : Hp ∈ (stateBefore x (slotStart S (s + 1)) q).S.T :=
    walk_end_mem_T _ _ _ Hp hEnd hinv.2.2.2.1
      (lem57_justification_cache_and_record S Sched x _ q).2.2.1
  have hσH := hCSC Hp hHT
  have hValidChain : ∀ Y : Block V, Y.AncestorEq Hp → Y ≠ Block.genesis →
      ∀ a' ∈ Y.attestations, valid_attestation (chainStateOf S.C Y.parent) a' = true := by
    intro Y hY hne a' ha'
    have hYT := ancestors_mem_T_of_exec S Sched x _ q Hp Y hHT hY
    have hpT := parent_mem_T_of_exec S Sched x _ q Y hYT hne
    rw [← hCSC _ hpT]
    exact hAV Y hYT hne a' ha'
  -- every pool attestation at `H'`'s height naming its `T_h` is counted on `H'`'s chain, or
  -- included in `B'`
  have hcount : ∀ a ∈ (stateBefore x (slotStart S (s + 1)) q).S.attestations,
      a.h = (chainStateOf S.C Hp).h → a.T = (chainStateOf S.C Hp).T_h.root →
      (a.val_index ∈ (chainStateOf S.C Hp).progress ∧
        (a.τ = false → a.val_index ∈ (chainStateOf S.C Hp).target_participation)) ∨
      a ∈ B'.attestations := by
    intro a ha hh hT
    cases hon : on_chain a Hp
    · right
      have hval : valid_attestation ((stateBefore x (slotStart S (s + 1)) q).S.σ Hp) a = true := by
        rw [hσH]
        exact GoldilocksCorrectness.Statements.Routines.valid_attestation_of_height _ a hh hT
      rw [hatts]
      exact GoldilocksCorrectness.Statements.Routines.lem52_pool_attestation_included _ Hp a ha
        hval hon
    · exact Or.inl (on_chain_counted S.C Hp a hon hValidChain hh)
  obtain ⟨h1, h2⟩ := quorum_certificate_with_counted S.C (chainStateOf S.C Hp) B' Q hQ
    (fun u hu => by
      obtain ⟨a, ha, hau, hh, hT⟩ := hPool u hu
      rcases hcount a ha hh hT with ⟨hp, -⟩ | hin
      · exact Or.inl (hau ▸ hp)
      · exact Or.inr ⟨a, hin, hau, hh, hT⟩)
  rw [hst]
  refine ⟨h1, fun hT => ?_⟩
  obtain ⟨k1, k2, -⟩ := h2 (fun u hu => by
    obtain ⟨a, ha, hau, hh, hT', hτ⟩ := hT u hu
    rcases hcount a ha hh hT' with ⟨-, hp⟩ | hin
    · exact Or.inl (hau ▸ hp hτ)
    · exact Or.inr ⟨a, hin, hau, hh, hT', hτ⟩)
  exact ⟨k1, k2⟩

end GoldilocksCorrectness.Proofs.Executions
