module
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements
public import GoldilocksCorrectness.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-!
# The honest corollaries of accountable safety

Under `Unforgeability Vocab.goldilocks Sched x.toTrace`, an attestation included on the chain of a block some validator holds,
its validator outside the adversary set up to the step, has its content in that validator's own
record (Lemma 74): the block was put on the wire by its holder, unforgeability puts the
attestation on the wire under its own validator's signature, which came from that validator's
tick (`attestation_from_own_tick`), and the record only grows. A validator's record is consistent
(`recordConsistent_of_exec`), and a consistent record holds no E1 and no E2 pair
(`no_slashable_of_consistent`). So when fewer than a third of the validators have been in the
adversary set up to the later of two steps' times, a set of at least `2q − n` validators holds one
that has never been in it, and the slashable sets of Lemma 73 and Lemma 71 cannot exist:

- Lemma 75: two node states read at two steps finalize compatible blocks, or two different blocks
  of their two trees share a root;
- Lemma 76: two justification certificates at one height on the chains of two held blocks name
  blocks with the same root; Lemma 76 (b): when those blocks are held, they are one block, or two
  different held blocks share a root.

## The kit

- `on_chain_iff`; `included_attestation_recorded`, Lemma 74's form for an attestation the held
  block itself includes; `content_mem_record_at`;
- `exists_honestThroughTime_of_card`, `time_max_le`;
- `not_slashable_of_held`: two attestations of one validator, each on the chain of a block held at
  a step at most `k`, that validator outside the adversary set up to the time after `k` steps,
  form no E1 and no E2 pair.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Proofs.Routines (on_chain_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (E1 E2 JustificationCertOn RootCollisionIn
  no_slashable_of_consistent lem71_one_justification_per_height lem65b_quorum_threshold)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_node_iff
  ancestorEq_genesis_iff on_chain_node_of_mem on_chain_node_of_parent)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- **Lemma 74's form for an included attestation.** Under unforgeability, an attestation that a
block `w` holds after `j` steps includes, its validator outside the adversary set up to the time
after `j` steps, has its content in that validator's record after `j` steps.

Why: the block is not the genesis block, which includes no attestation, so `w` put it on the wire
at an earlier step; unforgeability puts the attestation on the wire under its own validator's
signature by then, and it came from that validator's tick, whose record holds its content and
only grows.

The variables:
- `x`: the execution; `hU`: unforgeability; `j`: the step; `w`: the holder; `B`: the block;
  `a`: the attestation. -/
theorem included_attestation_recorded (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {j : ℕ} {w : V} {B : Block V} {a : Attestation V}
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x[j][w].st).S.T)
    -- `B` includes `a`
    (ha : a ∈ B.attestations)
    (hH : HonestThrough x j a.val_index) :
    a.content ∈ (x[j][a.val_index].st).Λ.sent := by
  have hg : B ≠ Block.genesis := by
    rintro rfl
    exact absurd ha List.not_mem_nil
  obtain ⟨i, hi, hsend, -, -⟩ := tree_block_relayed x hB hg
  have hH1 : HonestThrough x (i + 1) a.val_index := honestThrough_of_le x (by omega) hH
  have hown := hU.carried (i + 1) ⟨w, .block B⟩ (.attest a) a.val_index
    (mem_sent_of_mem_sub x hsend) (Or.inr ⟨a, ha, rfl⟩) rfl hH1
  obtain ⟨k', hk', -, -, -, hrec⟩ := attestation_from_own_tick S Sched x hU (i + 1) a hown hH1
  exact record_sent_mono x a.val_index (by omega) hrec

/-- **Lemma 74, honest attestations are recorded.** The proof; the audited statement is in
`Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `j`: the step;
  `w`: the holder; `B`: the block; `a`: the attestation. -/
theorem lem74_honest_attestations_recorded (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (j : ℕ) (w : V)
    (B : Block V) (a : Attestation V)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x[j][w].st).S.T)
    -- `a` is included in `B` or in an ancestor of `B`
    (ha : on_chain a B = true)
    (hH : HonestThrough x j a.val_index) :
    a.content ∈ (x[j][a.val_index].st).Λ.sent := by
  obtain ⟨X, hX, haX⟩ := (on_chain_iff a B).1 ha
  exact included_attestation_recorded x hU (ancestors_mem_T_of_exec S Sched x j w B X hB hX)
    haX hH

/-- Lemma 74 read at a later step: an attestation included on the chain of a block `w` holds
after `i` steps, its validator outside the adversary set up to the time after `k ≥ i` steps, has
its content in that validator's record after `k` steps.

The variables:
- `x`: the execution; `hU`: unforgeability; `i ≤ k`: the two steps; `w`: the holder; `B`: the
  block; `a`: the attestation. -/
theorem content_mem_record_at (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    {i k : ℕ} {w : V} {B : Block V} {a : Attestation V} (hik : i ≤ k)
    -- `w`'s tree holds `B` after `i` steps
    (hB : B ∈ (x[i][w].st).S.T)
    -- `a` is included in `B` or in an ancestor of `B`
    (ha : on_chain a B = true)
    (hH : HonestThrough x k a.val_index) :
    a.content ∈ (x[k][a.val_index].st).Λ.sent :=
  record_sent_mono x a.val_index hik
    (lem74_honest_attestations_recorded S Sched x hU i w B a hB ha (honestThrough_of_le x hik hH))

omit [DecidableEq V] [RootOrder] in
/-- A set of at least `2q − n` validators holds one outside the adversary set at every time up to
`t`, when fewer than a third of the validators have been in the adversary set up to `t`.

Why: otherwise every member has been in the adversary set at some time up to `t`, so the set has
fewer than a third of the validators, while `2q − n` is at least a third (Lemma 65 (b)).

The variables:
- `Sched`: the schedule; `t`: the time; `A`: the set of validators. -/
theorem exists_honestThroughTime_of_card (Sched : Schedule V) {t : Int}
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) t) {A : Finset V}
    -- `A` has at least `2q − n` members
    (hA : 2 * quorum V - validator_count V ≤ |A|) :
    ∃ v ∈ A, HonestThroughTime Sched t v := by
  by_contra hno
  have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ t ∧ v ∈ Sched.adv t' := by
    intro v hv
    by_contra hn
    exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
  have h3 := hAdv A hall
  have h65 := (lem65b_quorum_threshold (V := V)).1
  omega

/-- The time after `max i j` steps is at most the later of the times after `i` and after `j`
steps.

The variables:
- `x`: the execution; `i`, `j`: the two steps. -/
theorem time_max_le (x : AtomicExec (protocol S) Sched) (i j : ℕ) :
    (x[max i j].time : Int) ≤ max (x[i].time : Int) (x[j].time : Int) := by
  rcases le_total i j with h | h
  · rw [max_eq_right h]
    exact le_max_right _ _
  · rw [max_eq_left h]
    exact le_max_left _ _

/-- Under unforgeability, two attestations of one validator `v`, each included on the chain of a
block held at a step at most `k`, `v` outside the adversary set up to the time after `k` steps,
form no E1 and no E2 pair.

Why: both contents are in `v`'s record after `k` steps (Lemma 74), which is consistent.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `v`: the validator; `a`, `a'`: the two attestations. -/
theorem not_slashable_of_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {k : ℕ} {v : V}
    (hH : HonestThrough x k v) {a a' : Attestation V}
    -- both attestations are `v`'s
    (hav : a.val_index = v) (ha'v : a'.val_index = v)
    -- `a` is included on the chain of a block held at a step at most `k`
    (ha : ∃ i ≤ k, ∃ w : V, ∃ B ∈ (x[i][w].st).S.T, on_chain a B = true)
    -- `a'` is included on the chain of a block held at a step at most `k`
    (ha' : ∃ i ≤ k, ∃ w : V, ∃ B ∈ (x[i][w].st).S.T, on_chain a' B = true) :
    ¬ E1 a a' ∧ ¬ E2 a a' := by
  obtain ⟨i, hik, w, B, hB, hon⟩ := ha
  obtain ⟨i', hik', w', B', hB', hon'⟩ := ha'
  have hc := content_mem_record_at x hU hik hB hon (by rw [hav]; exact hH)
  have hc' := content_mem_record_at x hU hik' hB' hon' (by rw [ha'v]; exact hH)
  rw [hav] at hc
  rw [ha'v] at hc'
  exact no_slashable_of_consistent _ (recordConsistent_of_exec S Sched x k v) a a' hc hc'

/-- **Lemma 75, honest finalized blocks are compatible.** The proof; the audited statement is in
`Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators. -/
theorem lem75_honest_finalized_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int))) :
    (x[i][p₁].st).S.F.compatible (x[j][p₂].st).S.F = true ∨
      RootCollisionIn ((x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) := by
  by_cases hc : (x[i][p₁].st).S.F.compatible (x[j][p₂].st).S.F = true
  · exact Or.inl hc
  rcases lem73_accountable_safety S Sched x i j p₁ p₂ (Bool.eq_false_iff.2 hc) with
    ⟨b₁, hb₁, b₂, hb₂, A, hA, hs⟩ | hcol
  · exfalso
    obtain ⟨v, hvA, hHv⟩ := exists_honestThroughTime_of_card Sched hAdv hA
    obtain ⟨a, a', hav, ha'v, hon, hE⟩ := hs v hvA
    have hHk : HonestThrough x (max i j) v := honestThrough_of_time_le x hHv (time_max_le x i j)
    have h₁ : ∀ c : Attestation V, on_chain c b₁ = true →
        ∃ i' ≤ max i j, ∃ w : V, ∃ B ∈ (x[i'][w].st).S.T, on_chain c B = true :=
      fun c hcB => ⟨i, le_max_left i j, p₁, b₁, hb₁, hcB⟩
    have h₂ : ∀ c : Attestation V, on_chain c b₂ = true →
        ∃ i' ≤ max i j, ∃ w : V, ∃ B ∈ (x[i'][w].st).S.T, on_chain c B = true :=
      fun c hcB => ⟨j, le_max_right i j, p₂, b₂, hb₂, hcB⟩
    obtain ⟨hE1, hE2⟩ : ¬ E1 a a' ∧ ¬ E2 a a' := by
      rcases hon with ⟨ha, ha'⟩ | ⟨ha', ha⟩
      · exact not_slashable_of_held S Sched x hU hHk hav ha'v (h₁ a ha) (h₂ a' ha')
      · exact not_slashable_of_held S Sched x hU hHk hav ha'v (h₂ a ha) (h₁ a' ha')
    rcases hE with h | h
    · exact hE1 h
    · exact hE2 h
  · exact Or.inr hcol

/-- **Lemma 76, one justification per height among honest validators.** The proof; the audited
statement is in `Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks. -/
theorem lem76_honest_one_justification (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x[i][p₁].st).S.T)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x[j][p₂].st).S.T)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn B₂ h T') :
    T.root = T'.root := by
  rcases lem71_one_justification_per_height B₁ B₂ h T T' hJ hJ' with ⟨A, hA, hs⟩ | hroot
  · exfalso
    obtain ⟨v, hvA, hHv⟩ := exists_honestThroughTime_of_card Sched hAdv hA
    obtain ⟨a, a', hav, ha'v, ha, ha', hE2⟩ := hs v hvA
    have hHk : HonestThrough x (max i j) v := honestThrough_of_time_le x hHv (time_max_le x i j)
    exact (not_slashable_of_held S Sched x hU hHk hav ha'v
      ⟨i, le_max_left i j, p₁, B₁, hB₁, ha⟩ ⟨j, le_max_right i j, p₂, B₂, hB₂, ha'⟩).2 hE2
  · exact hroot

/-- **Lemma 76 (b), one justified block per height among honest validators.** The proof; the
audited statement is in `Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks. -/
theorem lem76b_honest_one_justification_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x[i][p₁].st).S.T)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x[j][p₂].st).S.T)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn B₂ h T')
    -- `T` is in one of the two trees
    (hT : T ∈ (x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T)
    -- `T'` is in one of the two trees
    (hT' : T' ∈ (x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) :
    T = T' ∨ RootCollisionIn ((x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) := by
  by_cases hTT : T = T'
  · exact Or.inl hTT
  · exact Or.inr ⟨T, hT, T', hT',
      lem76_honest_one_justification S Sched x hU i j p₁ p₂ hAdv B₁ B₂ hB₁ hB₂ h T T' hJ hJ', hTT⟩

end GoldilocksCorrectness.Proofs.Executions
