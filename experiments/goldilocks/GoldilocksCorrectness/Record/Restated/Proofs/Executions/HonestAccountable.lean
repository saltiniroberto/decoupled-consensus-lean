module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Accountable
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableStatementsChains
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Accountable
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableStatementsValidatorClient

@[expose] public section

/-!
# HonestAccountable, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/HonestAccountable.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the honest corollaries of
accountable safety, Lemma 74 (an attestation on a held block's chain, its validator honest, is in
that validator's record), Lemma 75 and Lemma 76. The page's routine-level theorems are the facts'
fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Statements.Routines (E1 E2 RootCollisionIn lem65b_quorum_threshold)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_node_iff
  ancestorEq_genesis_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 74's form for an included attestation.** Under unforgeability, an attestation that a
block `w` holds after `j` steps includes, its validator outside the adversary set up to the time
after `j` steps, has its content in that validator's record after `j` steps.

Why: the block is not the genesis block, which includes no attestation, so `w` put it on the wire
at an earlier step; unforgeability puts the attestation on the wire under its own validator's
signature by then, and it came from that validator's tick, whose record holds its content and
only grows.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `hU`: unforgeability; `j`: the step; `w`: the holder; `B`: the block;
  `a`: the attestation.

Read aloud: under unforgeability, an attestation that a block `w` holds after `j` steps includes,
its validator honest through that step, has its content in that validator's record then. -/
theorem included_attestation_recorded (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {j : ℕ} {w : V} {B : Block V}
    {a : Attestation V}
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x.st j w).tree)
    -- `B` includes `a`
    (ha : a ∈ B.attestations)
    (hH : x.HonestThrough A j a.val_index) :
    a.content ∈ (x.st j a.val_index).sentAttestations := by
  have hg : B ≠ Block.genesis := by
    rintro rfl
    exact absurd ha List.not_mem_nil
  obtain ⟨i, hi, hsend, -, -⟩ := (tree_block_relayed M F) x R E hB hg
  have hH1 : x.HonestThrough A (i + 1) a.val_index := (honestThrough_of_le M F) x R (by omega) hH
  have hown := (sent_unforgeable M F) R E (i + 1) ⟨w, .block B⟩ (.attest a) a.val_index
    ((mem_sent_of_mem_sub M F) x hsend) (Or.inr (Or.inr ⟨a, ha, rfl⟩)) rfl hH1
  obtain ⟨k', hk', -, -, -, hrec⟩ := (attestation_from_own_tick M F) S A x R E (i + 1) a hown hH1
  exact (record_sent_mono M F) x R E a.val_index (by omega) hrec

/-- **Lemma 74, honest attestations are recorded.** The proof; the audited statement is in
`Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `j`: the step;
  `w`: the holder; `B`: the block; `a`: the attestation.

Read aloud: an attestation included on the chain of a block some validator holds, its validator
never in the adversary set up to now, is in that validator's own record. -/
theorem lem74_honest_attestations_recorded (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (j : ℕ) (w : V)
    (B : Block V) (a : Attestation V)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x.st j w).tree)
    -- `a` is included in `B` or in an ancestor of `B`
    (ha : M.on_chain a B = true)
    (hH : x.HonestThrough A j a.val_index) :
    a.content ∈ (x.st j a.val_index).sentAttestations := by
  obtain ⟨X, hX, haX⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_iff M F) a B).1 ha
  exact (included_attestation_recorded M F) x R E ((GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E j w B X hB hX)
    haX hH

/-- Lemma 74 read at a later step: an attestation included on the chain of a block `w` holds
after `i` steps, its validator outside the adversary set up to the time after `k ≥ i` steps, has
its content in that validator's record after `k` steps.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `hU`: unforgeability; `i ≤ k`: the two steps; `w`: the holder; `B`: the
  block; `a`: the attestation.

Read aloud: an attestation included in a block held after `i` steps or in an ancestor of it, its
validator honest through step `k ≥ i`, has its content in that validator's record after `k` steps.
-/
theorem content_mem_record_at (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i k : ℕ} {w : V} {B : Block V} {a : Attestation V} (hik : i ≤ k)
    -- `w`'s tree holds `B` after `i` steps
    (hB : B ∈ (x.st i w).tree)
    -- `a` is included in `B` or in an ancestor of `B`
    (ha : M.on_chain a B = true)
    (hH : x.HonestThrough A k a.val_index) :
    a.content ∈ (x.st k a.val_index).sentAttestations :=
  (record_sent_mono M F) x R E a.val_index hik
    ((lem74_honest_attestations_recorded M F) S A x R E i w B a hB ha ((honestThrough_of_le M F) x R hik hH))

omit [RootOrder] in
/-- A set of at least `2q − n` validators holds one outside the adversary set at every time up to
`t`, when fewer than a third of the validators have been in the adversary set up to `t`.

Why: otherwise every member has been in the adversary set at some time up to `t`, so the set has
fewer than a third of the validators, while `2q − n` is at least a third (Lemma 65 (b)).

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `t`: the time; `A`: the set of validators.

Read aloud: when fewer than a third of the validators have been in the adversary set up to `t`, a
set of at least `2q − n` validators holds one outside it at every time up to `t`. -/
theorem exists_honestThroughTime_of_card (Act : Activity V) (x : Trace V (NamedObject V) M.N) {t : ℝ}
    (hAdv : Act.AdversaryFewerThanThirdUntil x (validator_count V) t) {A : Finset V}
    -- `A` has at least `2q − n` members
    (hA : 2 * quorum V - validator_count V ≤ |A|) :
    ∃ v ∈ A, Act.HonestThroughTime x t v := by
  by_contra hno
  have hall : ∀ v ∈ A, ∃ i : ℕ, x.time i ≤ t ∧ v ∈ Act.corrupted i := by
    intro v hv
    by_contra hn
    exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
  have h3 := hAdv A hall
  have h65 := (lem65b_quorum_threshold (V := V)).1
  omega

/-- The time after `max i j` steps is at most the later of the times after `i` and after `j`
steps.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`, `j`: the two steps.

Read aloud: the time after `max i j` steps is at most the later of the times after `i` and `j`
steps. -/
theorem time_max_le (x : Trace V (NamedObject V) M.N) (i j : ℕ) :
    (x.time (max i j)) ≤ max (x.time i) (x.time j) := by
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
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `v`: the validator; `a`, `a'`: the two attestations.

Read aloud: two attestations of an honest validator, each included on the chain of a block held at a
step at most `k`, form no E1 and no E2 pair. -/
theorem not_slashable_of_held (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V}
    (hH : x.HonestThrough A k v) {a a' : Attestation V}
    -- both attestations are `v`'s
    (hav : a.val_index = v) (ha'v : a'.val_index = v)
    -- `a` is included on the chain of a block held at a step at most `k`
    (ha : ∃ i ≤ k, ∃ w : V, ∃ B ∈ (x.st i w).tree, M.on_chain a B = true)
    -- `a'` is included on the chain of a block held at a step at most `k`
    (ha' : ∃ i ≤ k, ∃ w : V, ∃ B ∈ (x.st i w).tree, M.on_chain a' B = true) :
    ¬ E1 a a' ∧ ¬ E2 a a' := by
  obtain ⟨i, hik, w, B, hB, hon⟩ := ha
  obtain ⟨i', hik', w', B', hB', hon'⟩ := ha'
  have hc := (content_mem_record_at M F) x R E hik hB hon (by rw [hav]; exact hH)
  have hc' := (content_mem_record_at M F) x R E hik' hB' hon' (by rw [ha'v]; exact hH)
  rw [hav] at hc
  rw [ha'v] at hc'
  exact (GoldilocksCorrectness.Record.Statements.Routines.no_slashable_of_consistent M F) _ ((GoldilocksCorrectness.Record.Statements.Executions.recordConsistent_of_exec M F) S A x R E k v) a a' hc hc'

/-- **Lemma 75, honest finalized blocks are compatible.** The proof; the audited statement is in
`Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators.

Read aloud: when signatures are unforgeable and fewer than a third of the validators have been
adversarial up to the later of the two times, any two finalized blocks are compatible, or two
different blocks of the two trees share a root. -/
theorem lem75_honest_finalized_compatible (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j))) :
    (x.st i p₁).finalized.compatible (x.st j p₂).finalized = true ∨
      RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) := by
  by_cases hc : (x.st i p₁).finalized.compatible (x.st j p₂).finalized = true
  · exact Or.inl hc
  rcases (lem73_accountable_safety M F Fx) S A x R E i j p₁ p₂ (Bool.eq_false_iff.2 hc) with
    ⟨b₁, hb₁, b₂, hb₂, Xs, hXs, hs⟩ | hcol
  · exfalso
    obtain ⟨v, hvA, hHv⟩ := (exists_honestThroughTime_of_card M F) A x hAdv hXs
    obtain ⟨a, a', hav, ha'v, hon, hE⟩ := hs v hvA
    have hHk : x.HonestThrough A (max i j) v := (honestThrough_of_time_le M F) x R hHv
      (by have := (time_max_le M F) x i j; exact_mod_cast this)
    have h₁ : ∀ c : Attestation V, M.on_chain c b₁ = true →
        ∃ i' ≤ max i j, ∃ w : V, ∃ B ∈ (x.st i' w).tree, M.on_chain c B = true :=
      fun c hcB => ⟨i, le_max_left i j, p₁, b₁, hb₁, hcB⟩
    have h₂ : ∀ c : Attestation V, M.on_chain c b₂ = true →
        ∃ i' ≤ max i j, ∃ w : V, ∃ B ∈ (x.st i' w).tree, M.on_chain c B = true :=
      fun c hcB => ⟨j, le_max_right i j, p₂, b₂, hb₂, hcB⟩
    obtain ⟨hE1, hE2⟩ : ¬ E1 a a' ∧ ¬ E2 a a' := by
      rcases hon with ⟨ha, ha'⟩ | ⟨ha', ha⟩
      · exact (not_slashable_of_held M F) S A x R E hHk hav ha'v (h₁ a ha) (h₂ a' ha')
      · exact (not_slashable_of_held M F) S A x R E hHk hav ha'v (h₂ a ha) (h₁ a' ha')
    rcases hE with h | h
    · exact hE1 h
    · exact hE2 h
  · exact Or.inr hcol

/-- **Lemma 76, one justification per height among honest validators.** The proof; the audited
statement is in `Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks.

Read aloud: under the same two assumptions, two justification certificates at one height, on the
chains of two held blocks, name blocks with the same root. -/
theorem lem76_honest_one_justification (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x.st i p₁).tree)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x.st j p₂).tree)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn M B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn M B₂ h T') :
    T.root = T'.root := by
  rcases (GoldilocksCorrectness.Record.Statements.Routines.lem71_one_justification_per_height M F Fx) B₁ B₂ h T T' hJ hJ' with ⟨Xs, hXs, hs⟩ | hroot
  · exfalso
    obtain ⟨v, hvA, hHv⟩ := (exists_honestThroughTime_of_card M F) A x hAdv hXs
    obtain ⟨a, a', hav, ha'v, ha, ha', hE2⟩ := hs v hvA
    have hHk : x.HonestThrough A (max i j) v := (honestThrough_of_time_le M F) x R hHv
      (by have := (time_max_le M F) x i j; exact_mod_cast this)
    exact ((not_slashable_of_held M F) S A x R E hHk hav ha'v
      ⟨i, le_max_left i j, p₁, B₁, hB₁, ha⟩ ⟨j, le_max_right i j, p₂, B₂, hB₂, ha'⟩).2 hE2
  · exact hroot

/-- **Lemma 76 (b), one justified block per height among honest validators.** The proof; the
audited statement is in `Statements/Executions/HonestAccountableStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks.

Read aloud: two held blocks justified at one height on the chains of two held blocks are one block,
or two different held blocks share a root. -/
theorem lem76b_honest_one_justification_block (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x.st i p₁).tree)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x.st j p₂).tree)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn M B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn M B₂ h T')
    -- `T` is in one of the two trees
    (hT : T ∈ (x.st i p₁).tree ∪ (x.st j p₂).tree)
    -- `T'` is in one of the two trees
    (hT' : T' ∈ (x.st i p₁).tree ∪ (x.st j p₂).tree) :
    T = T' ∨ RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) := by
  by_cases hTT : T = T'
  · exact Or.inl hTT
  · exact Or.inr ⟨T, hT, T', hT',
      (lem76_honest_one_justification M F Fx) S A x R E i j p₁ p₂ hAdv B₁ B₂ hB₁ hB₂ h T T' hJ hJ', hTT⟩

end GoldilocksCorrectness.Record.Proofs.Executions

