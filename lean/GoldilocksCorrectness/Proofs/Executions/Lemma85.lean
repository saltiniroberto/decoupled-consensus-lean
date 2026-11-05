module
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit

@[expose] public section

/-!
# Lemma 85: every honest finalized block is on the honest chain

The proof of `lem85_honest_finalized_on_chain`, stated in
`GoldilocksCorrectness/Statements/Executions/HealedCachesStatements.lean`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem66_chain_state_certified)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- An ancestor of a block on the honest chain is on the honest chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `B`, `B'`: the two blocks. -/
theorem onHonestChain_of_ancestorEq {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s₀ : ℕ} {B B' : Block V}
    -- `B'` is on the honest chain
    (h : OnHonestChain S Sched x s₀ B')
    -- `B` is `B'` or an ancestor of it
    (hBB : B.AncestorEq B') : OnHonestChain S Sched x s₀ B := by
  obtain ⟨s, hs, u, hu, C', hC', hB'C⟩ := h
  exact ⟨s, hs, u, hu, C', hC', ancestorEq_trans hBB hB'C⟩

/-- **Kit fact, the justified block of an honest state is on the chain at a slot whose update ran
by then.** Under unforgeability, when fewer than a quorum of validators are ever in the adversary
set, every honest attestation sent at or after `t₀` names the honest chain's entry at its height,
every honest attestation sent before `t₀` has height at most `H`, and roots name blocks among what
honest validators hold by the time of step `i`: if `v` is honest at the time of step `i` and its
justification height after `i` steps is greater than `H`, its justified block is on the honest
chain at a slot `s_a` whose support cutoff of slot `s_a + 1` is at most the time of step `i`.

Why: the justified block is that of the chain state of a block `D` of `v`'s tree, with its
justification certificate on `D`'s chain (Lemma 66); the certificate names by its root an entry of
the honest chain at a slot whose update ran by the time of step `i` (Lemma 83); `v` holds the
justified block, and the entry is held by then, so the two are one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i`: the step;
  `v`: the validator.

Read aloud: an honest justified block above the threshold is on the honest chain at a slot whose
update ran by then. -/
theorem justified_onHonestChainAt_of_caches (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i : ℕ) (v : V)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[i].time)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    (hv : v ∉ Sched.adv (x[i].time : Int))
    (hH : H < (x[i][v].st).S.h_j) :
    ∃ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ s_a (x[i][v].st).S.J := by
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x i v
  have h1 : 1 ≤ (chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := (lem66_chain_state_certified S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, E, hcut, hE, -, -, hroot⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem83_one_justification_greater_than_threshold
      S Sched x s₀ t₀ H i v D _ _ hU (hAdvQ _) hAgree
      (GoldilocksCorrectness.Statements.Executions.oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost
        S Sched x t₀ _ H hOld) hD hJC hH
  have hJT : (x[i][v].st).S.J ∈ (x[i][v].st).S.T :=
    (lem57_justification_cache_and_record S Sched x i v).2.2.1
  have hEq : (x[i][v].st).S.J = E := hRoots _ _ ⟨i, v, hv, le_rfl, hJT⟩
    (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hE hcut) hroot
  exact ⟨s_a, hcut, by rw [hEq]; exact hE⟩

/-- An ancestor of a block on the honest chain at a slot is on the honest chain at that slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `s`: the slot; `B`, `B'`: the two blocks. -/
theorem onHonestChainAt_of_ancestorEq {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s₀ s : ℕ} {B B' : Block V}
    -- `B'` is on the honest chain at slot `s`
    (h : OnHonestChainAt S Sched x s₀ s B')
    -- `B` is `B'` or an ancestor of it
    (hBB : B.AncestorEq B') : OnHonestChainAt S Sched x s₀ s B := by
  obtain ⟨hs, u, hu, C', hC', hB'C⟩ := h
  exact ⟨hs, u, hu, C', hC', ancestorEq_trans hBB hB'C⟩

/-- **Lemma 85, keeping the slot.** The proof; the audited statement is in
`Statements/Executions/HealedCachesStatements.lean`. Lemma 85 with the slot of the honest chain
named: the finalized block of a validator honest at a step at a time at most `t` is on the honest
chain at a slot `s_a` whose support cutoff of slot `s_a + 1` is at most the later of the time of
that step and the time of step `i₁`.

Why: at a step from `i₁` on, the finalized block is the justified block or an ancestor of it
(Lemma 84), and the justified block is on the chain at a slot whose update ran by then
(`justified_onHonestChainAt_of_caches`). At an earlier step, the finalized block is that of the
chain state of a held block `B`, at the height `h_F`. When `h_F > H`, its justification
certificate on `B`'s chain names the honest chain's entry at `h_F` at such a slot (Lemmas 66 and
83), and the two blocks, in honest trees, are one. When `h_F ≤ H`, some validator `w` is honest at
`i₁`, its justified block is on the chain at a slot whose update ran by the time of step `i₁`, at a
height greater than `H`, so greater than `h_F`: Lemma 68's honest corollary makes the finalized
block an ancestor of it, or that block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.

Roots name blocks until `max t x[i₁].time`, as Lemma 85's. -/
theorem lem85_honest_finalized_on_chain_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i₁ t : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (max t x[i₁].time))
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i₁].time : Int))
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    (hStart : ∀ v : V, v ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][v].st)) :
    ∀ (i : ℕ) (v : V), x[i].time ≤ t → v ∉ Sched.adv (x[i].time : Int) →
      ∃ s_a : ℕ, supportCutoff S (s_a + 1) ≤ max x[i].time x[i₁].time ∧
        OnHonestChainAt S Sched x s₀ s_a (x[i][v].st).S.F := by
  intro i v ht hv
  have hit : x[i].time ≤ max t x[i₁].time := le_trans ht (le_max_left _ _)
  rcases Nat.lt_or_ge i i₁ with hlt | hge
  swap
  · have hC := lem84_caches_stay_on_chain S Sched x s₀ t₀ H i₁ t hU hMono
      (hRoots.mono (le_max_left _ _)) hAdvQ hAgree hOld hStart i v hge ht hv
    obtain ⟨s_a, hcut, hJ⟩ := justified_onHonestChainAt_of_caches S Sched x s₀ t₀ H i v hU hMono
      (hRoots.mono hit) hAdvQ hAgree hOld hv hC.1
    exact ⟨s_a, le_trans hcut (le_max_left _ _), onHonestChainAt_of_ancestorEq hJ hC.2.2.2.2⟩
  · obtain ⟨B, hB, hFB⟩ :=
      GoldilocksCorrectness.Statements.Executions.finalizedFromChain_of_exec S Sched x i v
    rw [hFB]
    rcases Nat.lt_or_ge H (chainStateOf S.C B).h_F with hgt | hle
    · -- the finalization height is greater than `H`: the certificate names the chain's entry
      obtain ⟨hcert, -, hFBanc, -⟩ := (lem66_chain_state_certified S.C B).2.2
        (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hgt))
      obtain ⟨s_a, E, hcut, hE, -, -, hroot⟩ :=
        GoldilocksCorrectness.Statements.Executions.lem83_one_justification_greater_than_threshold
          S Sched x s₀ t₀ H i v B _ _ hU (hAdvQ _) hAgree
          (GoldilocksCorrectness.Statements.Executions.oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost
            S Sched x t₀ _ H hOld) hB hcert hgt
      have hFT := ancestors_mem_T_of_exec S Sched x i v B _ hB hFBanc
      have hEq : (chainStateOf S.C B).F = E := hRoots _ _ ⟨i, v, hv, hit, hFT⟩
        (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hE (le_trans hcut hit)) hroot
      rw [hEq]
      exact ⟨s_a, le_trans hcut (le_max_left _ _), hE⟩
    · -- the finalization height is at most `H`: compare with an honest justified block at `i₁`
      obtain ⟨w, hw⟩ : ∃ w : V, w ∉ Sched.adv (x[i₁].time : Int) := by
        by_contra hall
        have hall' : ∀ w ∈ (Finset.univ : Finset V),
            ∃ t' : Int, t' ≤ (x[i₁].time : Int) ∧ w ∈ Sched.adv t' := by
          intro w _
          by_contra hn
          exact hall ⟨w, fun hadv => hn ⟨_, le_rfl, hadv⟩⟩
        have h3 := hThird Finset.univ hall'
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
        rw [Finset.card_univ] at h3
        unfold validator_count at h3
        omega
      obtain ⟨hHw, -, -, hJh, -⟩ := hStart w hw
      obtain ⟨s_a, hcut, hJw⟩ := justified_onHonestChainAt_of_caches S Sched x s₀ t₀ H i₁ w hU
        hMono (hRoots.mono (le_max_right _ _)) hAdvQ hAgree hOld hw hHw
      have hJT : (x[i₁][w].st).S.J ∈ (x[i₁][w].st).S.T :=
        (lem57_justification_cache_and_record S Sched x i₁ w).2.2.1
      have hmax : max (x[i].time : Int) (x[i₁].time : Int) = (x[i₁].time : Int) :=
        max_eq_right (Int.ofNat_le.2 (time_mono x hlt.le))
      have hF := GoldilocksCorrectness.Statements.Executions.lem68_honest_past_finalized S Sched x
        hU hRoots i i₁ v w B _ (by rw [hmax]; exact hThird) hv hw hB hJT
        (by rw [hJh]; exact lt_of_le_of_lt hle hHw) (max_le hit (le_max_right _ _))
      exact ⟨s_a, le_trans hcut (le_max_right _ _), onHonestChainAt_of_ancestorEq hJw hF⟩

/-- **Lemma 85, every honest finalized block is on the honest chain.** The proof; the audited
statement is in `Statements/Executions/HealedCachesStatements.lean`. It is
`lem85_honest_finalized_on_chain_at` with the slot dropped.

Why: at a step from `i₁` on, the finalized block is the justified block or an ancestor of it,
which is on the chain (Lemma 84). At an earlier step, the finalized block is that of the chain
state of a held block `B`, at the height `h_F`. When `h_F > H`, its justification certificate on
`B`'s chain names the honest chain's entry at `h_F` (Lemmas 66 and 83), and the two blocks, in
honest trees, are one. When `h_F ≤ H`, some validator `w` is honest at `i₁`, and its justified
block, on the chain, is at a height greater than `H`, so greater than `h_F`: Lemma 68's honest
corollary makes the finalized block an ancestor of it, or that block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.

Roots name blocks until `max t x[i₁].time`: the conclusion is for the steps at times at most `t`;
at a step `i` from `i₁` on the proof reads Lemma 84 up to `t`; at a step `i` before `i₁` it compares
the finalized block, held after `i` steps, with the entry of the honest chain at a slot whose update
ran by `x[i].time` (Lemma 83), and, by Lemma 89a, with `w`'s justified block after `i₁` steps. -/
theorem lem85_honest_finalized_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i₁ t : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (max t x[i₁].time))
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i₁].time : Int))
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    (hStart : ∀ v : V, v ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][v].st)) :
    ∀ (i : ℕ) (v : V), x[i].time ≤ t → v ∉ Sched.adv (x[i].time : Int) →
      OnHonestChain S Sched x s₀ (x[i][v].st).S.F := fun i v ht hv =>
  let ⟨s_a, _, h⟩ := lem85_honest_finalized_on_chain_at S Sched x s₀ t₀ H i₁ t hU hMono hRoots
    hThird hAdvQ hAgree hOld hStart i v ht hv
  ⟨s_a, h⟩

end GoldilocksCorrectness.Proofs.Executions
