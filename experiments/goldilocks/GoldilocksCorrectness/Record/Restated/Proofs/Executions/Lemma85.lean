module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableStatementsChains
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit

@[expose] public section

/-!
# Lemma85, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma85.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the honest chain is closed under ancestors, the
justifications read from the finality caches are on the honest chain, and Lemma 85, every honest
finalized block is on the honest chain. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- An ancestor of a block on the honest chain is on the honest chain.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `B`, `B'`: the two blocks.

Read aloud: an ancestor of a block on the honest chain is on the honest chain. -/
theorem onHonestChain_of_ancestorEq {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {s₀ : ℕ} {B B' : Block V}
    -- `B'` is on the honest chain
    (h : OnHonestChain M S A x s₀ B')
    -- `B` is `B'` or an ancestor of it
    (hBB : B.AncestorEq B') : OnHonestChain M S A x s₀ B := by
  obtain ⟨s, hs, u, hu, C', hC', hB'C⟩ := h
  exact ⟨s, hs, u, hu, C', hC', ancestorEq_trans hBB hB'C⟩

/-- **Kit fact, the justified block of an honest state is on the chain at a slot whose update ran
by then.** Under unforgeability, when fewer than a quorum of validators are ever in the adversary
set, every honest attestation sent at or after `t₀` names the honest chain's entry at its height,
every honest attestation sent before `t₀` has height at most `H`, and roots name blocks among what
honest validators hold by the time of step `i`: if `v` is honest at the time of step `i` and its
justification height after `i` steps is greater than `H`, its justified block is on the honest
chain at a slot `s_a` whose update some validator ran at a step before `i`.

Why: the justified block is that of the chain state of a block `D` of `v`'s tree, with its
justification certificate on `D`'s chain (Lemma 66); the certificate names by its root the entry an
honest attester held at its own tick to the support cutoff of the next slot, a step before `i`, on the
honest chain at that slot; `v` holds the
justified block, and the attester held the entry by then, so the two are one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i`: the step;
  `v`: the validator.

Read aloud: an honest justified block above the threshold is on the honest chain at a slot whose
update ran by then. -/
theorem justified_onHonestChainAt_of_caches (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time i))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hv : v ∉ A.corrupted i)
    (hH : H < (x.st i v).justifiedHeight) :
    ∃ s_a : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
      OnHonestChainAt M S A x s₀ s_a (x.st i v).justified := by
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E i v
  have h1 : 1 ≤ (M.chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, hEb, hE, -, -, hroot⟩ :=
    (cert_entry_held_of_agree M F U Fx) S A x R s₀ t₀ H i v D _ _ E hAdvQ hAgree hOld hD hJC hH
  have hJT : (x.st i v).justified ∈ (x.st i v).tree :=
    ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i v).2.2.1
  -- the attester held the entry at its tick, a step before `i`: one root, so one block
  have hEq : (x.st i v).justified = Eb := hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hv le_rfl hJT)
    ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
      ((time_mono M) x R hk.le) hEb) hroot
  exact ⟨s_a, ⟨_, uₐ, hk, hl⟩, by rw [hEq]; exact hE⟩

/-- An ancestor of a block on the honest chain at a slot is on the honest chain at that slot.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot of the honest
  chain; `s`: the slot; `B`, `B'`: the two blocks.

Read aloud: an ancestor of a block on the honest chain at slot `s` is on the honest chain at slot
`s`. -/
theorem onHonestChainAt_of_ancestorEq {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} {s₀ s : ℕ} {B B' : Block V}
    -- `B'` is on the honest chain at slot `s`
    (h : OnHonestChainAt M S A x s₀ s B')
    -- `B` is `B'` or an ancestor of it
    (hBB : B.AncestorEq B') : OnHonestChainAt M S A x s₀ s B := by
  obtain ⟨hs, u, hu, C', hC', hB'C⟩ := h
  exact ⟨hs, u, hu, C', hC', ancestorEq_trans hBB hB'C⟩

/-- **Lemma 68's honest corollary, with the bound on the roots a real time.** The argument of
`lem68_honest_past_finalized` with its bound `tR` a real number: the roots name blocks among what
honest validators hold up to `tR`, and both steps are at times at most `tR`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tR`: the bound on the roots;
- `i`, `j`: the two steps; `p`, `w`: the two validators; `B`, `B'`: the blocks they hold.

Read aloud: when fewer than a third of the validators have been in the adversary set up to the
later of two steps' times, a block an honest validator holds at one step that is higher than the
finalization height of another block an honest validator holds at the other has that block's
finalized block as an ancestor, or is it, when roots name blocks up to a real time at least both
steps' times. -/
theorem honest_past_finalized_real (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℝ}
    (hRoots : RootsNameBlocksUntil M A x tR) (i j : ℕ) (p w : V) (B B' : Block V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j)))
    -- `p` is honest after `i` steps, and `w` after `j` steps
    (hp : p ∉ A.corrupted i) (hw : w ∉ A.corrupted j)
    -- `p` holds `B` after `i` steps, and `w` holds `B'` after `j` steps
    (hB : B ∈ (x.st i p).tree) (hB' : B' ∈ (x.st j w).tree)
    -- the chain-state height of `B'` is greater than the finalization height of `B`'s
    (hlt : (M.chainStateOf S.C B).h_F < (M.chainStateOf S.C B').h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max (x.time i) (x.time j) ≤ tR) :
    (M.chainStateOf S.C B).F.AncestorEq B' := by
  rcases (GoldilocksCorrectness.Record.Statements.Routines.lem68_past_finalized M F Fx) S.C B B' hlt with h | ⟨Q, hQ, hs⟩ | ⟨X, Y, hX, hY, hr, hne⟩
  · exact h
  · exfalso
    obtain ⟨u, huA, hHu⟩ := (exists_honestThroughTime_of_card M F) A x hThird hQ
    obtain ⟨a, a', hau, ha'u, ha, ha', hE1⟩ := hs u huA
    have hmax : x.time (max i j) ≤ max (x.time i) (x.time j) := by
      rcases le_total i j with h | h
      · rw [max_eq_right h]; exact le_max_right _ _
      · rw [max_eq_left h]; exact le_max_left _ _
    have hHk : x.HonestThrough A (max i j) u := (honestThrough_of_time_le M F) x R hHu hmax
    exact ((not_slashable_of_held M F) S A x R E hHk hau ha'u
      ⟨i, le_max_left i j, p, B, hB, ha⟩ ⟨j, le_max_right i j, w, B', hB', ha'⟩).1 hE1
  · exfalso
    have hmem : ∀ Z : Block V, (Z.AncestorEq B ∨ Z.AncestorEq B') → inHonestTreeBy M A x tR Z := by
      rintro Z (hZ | hZ)
      · exact ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := p) hp (le_of_max_le_left htR) ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i p B Z hB hZ))
      · exact ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := j) (v := w) hw (le_of_max_le_right htR) ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w B' Z hB' hZ))
    exact hne (hRoots X Y (hmem X hX) (hmem Y hY) hr)

/-- **Lemma 85, keeping the slot.** The proof; the audited statement is in
`Statements/Executions/HealedCachesStatements.lean`. Lemma 85 with the slot of the honest chain
named: the finalized block of a validator honest at a step at a time at most `t` is on the honest
chain at a slot `s_a` whose update some validator ran at a step before that step, or before step
`i₁` when that is later.

Why: at a step from `i₁` on, the finalized block is the justified block or an ancestor of it
(Lemma 84), and the justified block is on the chain at a slot whose update ran by then
(`justified_onHonestChainAt_of_caches`). At an earlier step, the finalized block is that of the
chain state of a held block `B`, at the height `h_F`. When `h_F > H`, its justification
certificate on `B`'s chain names the entry an honest attester held at its tick to such a slot's
next cutoff (Lemma 66, `cert_entry_held_of_agree`), and the two blocks, in honest trees, are one. When `h_F ≤ H`, some validator `w` is honest at
`i₁`, its justified block is on the chain at a slot whose update ran by the time of step `i₁`, at a
height greater than `H`, so greater than `h_F`: Lemma 68's honest corollary makes the finalized
block an ancestor of it, or that block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.

Roots name blocks until `max t x[i₁].time`, as Lemma 85's.

Read aloud: the block finalized in the node state of a validator honest at a step at a time at most
`t` is on the honest chain at a slot whose update ran by that step, or by step `i₁` when that is
later. -/
theorem lem85_honest_finalized_on_chain_at (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (max t (x.time i₁)))
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time i₁))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `max t (x.time i₁)` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (max t (x.time i₁)) t₀))
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    (hStart : ∀ v : V, v ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ (i : ℕ) (v : V), x.time i ≤ t → v ∉ A.corrupted i →
      ∃ s_a : ℕ, (∃ (k : ℕ) (u : V), k < max i i₁ ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
        OnHonestChainAt M S A x s₀ s_a (x.st i v).finalized := by
  intro i v ht hv
  have hit : x.time i ≤ max (t : ℝ) (x.time i₁) := le_trans ht (le_max_left _ _)
  rcases lt_or_ge (x.time i₁) (x.time i) with hgt | hle₁
  · -- `i` is at a later time than `i₁`: `v`, honest after `i`, is honest at the time of `i₁` (Lemma 84's helper)
    have hge : i₁ ≤ i := ((lt_of_time_lt M) x R hgt).le
    have hv₁ : v ∉ A.corruptedAtTime x (x.time i₁) := Activity.not_mem_corruptedAtTime.2 fun k hk =>
      E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_le_of_lt hk hgt)).le hv
    have hC := (lem84_caches_stay_on_chain_of_honest M F U Fx) S A x R s₀ t₀ H i₁ t E
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_left _ _) hRoots) (hAdvQ.mono (max_le_max (le_max_left _ _) le_rfl)) hAgree hOld hStart i v hv₁ hge ht hv
    obtain ⟨s_a, hcut, hJ⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀ t₀ H i v E
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hit hRoots) (hAdvQ.mono (max_le_max hit le_rfl)) hAgree hOld hv hC.1
    obtain ⟨k, u, hk, hl⟩ := hcut
    exact ⟨s_a, ⟨k, u, lt_of_lt_of_le hk (le_max_left _ _), hl⟩,
      (onHonestChainAt_of_ancestorEq M F) hJ hC.2.2.2.2⟩
  · obtain ⟨B, hB, hFB⟩ :=
      (GoldilocksCorrectness.Record.Statements.Executions.finalizedFromChain_of_exec M F) S A x R E i v
    rw [hFB]
    rcases Nat.lt_or_ge H (M.chainStateOf S.C B).h_F with hgt | hle
    · -- the finalization height is greater than `H`: the certificate names the chain's entry, which an
      -- honest attester held at its tick, a step before `i` (K1's shape,)
      obtain ⟨hcert, -, hFBanc, -⟩ := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C B).2.2
        (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le H) hgt))
      obtain ⟨s_a, uₐ, Eb, hk, hl, -, -, hEb, hE, -, -, hroot⟩ :=
        (cert_entry_held_of_agree M F U Fx) S A x R s₀ t₀ H i v B _ _ E
          (hAdvQ.mono (max_le_max hit le_rfl)) hAgree hOld hB hcert hgt
      have hFT := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i v B _ hB hFBanc
      have hEq : (M.chainStateOf S.C B).F = Eb := hRoots _ _ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := i) (v := v) hv hit hFT)
        ((onHonestChainAt_inHonestTreeBy M F U) S A x R E _ uₐ (M.supportCutoff S.C (s_a + 1)) _ Eb hl
          (le_trans ((time_mono M) x R hk.le) hit) hEb) hroot
      rw [hEq]
      exact ⟨s_a, ⟨_, uₐ, lt_of_lt_of_le hk (le_max_left _ _), hl⟩, hE⟩
    · -- the finalization height is at most `H`: compare with an honest justified block at `i₁`
      obtain ⟨w, hwT⟩ : ∃ w : V, w ∉ A.corruptedAtTime x (x.time i₁) := by
        by_contra hall
        have hall' : ∀ w ∈ (Finset.univ : Finset V),
            ∃ k : ℕ, x.time k ≤ x.time i₁ ∧ w ∈ A.corrupted k := by
          intro w _
          by_contra hn
          exact hall ⟨w, fun hadv => by
            obtain ⟨k, hk, hkc⟩ := Activity.mem_corruptedAtTime.1 hadv
            exact hn ⟨k, hk, hkc⟩⟩
        have h3 := hThird Finset.univ hall'
        have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
        rw [Finset.card_univ] at h3
        unfold validator_count at h3
        omega
      have hw : w ∉ A.corrupted i₁ := Activity.not_mem_corruptedAtTime.1 hwT i₁ le_rfl
      obtain ⟨hHw, -, -, hJh, -⟩ := hStart w hwT
      obtain ⟨s_a, hcut, hJw⟩ := (justified_onHonestChainAt_of_caches M F U Fx) S A x R s₀ t₀ H i₁ w
        E ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_max_right _ _) hRoots) (hAdvQ.mono (max_le_max (le_max_right _ _) le_rfl)) hAgree hOld hw hHw
      have hJT : (x.st i₁ w).justified ∈ (x.st i₁ w).tree :=
        ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E i₁ w).2.2.1
      have hmax : max (x.time i) (x.time i₁) = x.time i₁ :=
        max_eq_right hle₁
      have hF := (honest_past_finalized_real M F Fx) S A x R E
        hRoots i i₁ v w B _ (by rw [hmax]; exact hThird) hv hw hB hJT
        (by rw [hJh]; exact lt_of_le_of_lt hle hHw) (max_le hit (le_max_right _ _))
      obtain ⟨k, u, hk, hl⟩ := hcut
      exact ⟨s_a, ⟨k, u, lt_of_lt_of_le hk (le_max_right _ _), hl⟩,
        (onHonestChainAt_of_ancestorEq M F) hJw hF⟩

end GoldilocksCorrectness.Record.Proofs.Executions

