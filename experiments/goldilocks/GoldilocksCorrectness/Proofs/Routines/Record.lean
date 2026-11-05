module
public import GoldilocksCorrectness.Statements.Routines.RecordDefs
public import GoldilocksCorrectness.Proofs.Routines.Walk
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# Lemma 72: the anti-slashing record is consistent

The proofs of `lem72_initial_record_consistent` and `lem72_create_attestation_consistent`, stated in
`GoldilocksCorrectness/Statements/Routines/RecordStatements.lean`.

The route: one lemma per routine of the validator client, in the shape of a branch equation
(`finality_pair_some`, `own_lock_cases`, `height_pair_vote_cases`, `create_attestation_cases`) and
the four writes of `record_attestation` as field lemmas; then `record_attestation_consistent`, which
keeps `RecordConsistent` across `record_attestation` from four facts about the attestation written,
and the two lemmas.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type}

/-! ## The routines of the validator client -/

private theorem getElem_option (f : Height → Option BlockId) (h : Height) : f[h] = f h := rfl

private theorem getElem_bool (f : Height → Bool) (h : Height) : f[h] = f h := rfl

/-- When `finality_pair` returns a pair, it is `(h_j, J)`, `h_F < h_j`, and the record holds at
`h_j` no target other than `J`, no timeout and no lock other than `J`.

The variables:
- `Λ`: the record; `h_j`, `J`, `h_F`: the justification height, the justified root and the
  finalization height; `p`: the pair returned. -/
theorem finality_pair_some {Λ : SigningHistory} {h_j : Height} {J : BlockId} {h_F : Height}
    {p : FinalityPair} (hfp : finality_pair Λ h_j J h_F = some p) :
    p = ⟨h_j, J⟩ ∧ h_F < h_j ∧ (∀ T : BlockId, Λ.target h_j = some T → T = J) ∧
      Λ.timeout h_j = false ∧ (∀ T : BlockId, Λ.lock h_j = some T → T = J) := by
  simp only [finality_pair, Id.run, getElem_option, getElem_bool] at hfp
  split_ifs at hfp with h1 h2 h3 h4
  have hp : p = ⟨h_j, J⟩ := (Option.some.inj hfp).symm
  refine ⟨hp, Nat.lt_of_not_le h1, ?_, by simpa using h3, ?_⟩
  · intro T hT
    simp only [hT, ne_eq, reduceCtorEq, not_false_eq_true, decide_true, Option.some.injEq,
      decide_not, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      not_not] at h2
    exact h2
  · intro T hT
    simp only [hT, ne_eq, reduceCtorEq, not_false_eq_true, decide_true, Option.some.injEq,
      decide_not, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      not_not] at h4
    exact h4

/-- The lock `own_lock` reads at `h` is the record's lock at `h`, or the target of the finality
pair `fp` when `fp` is at `h`.

The variables:
- `Λ`: the record; `h`: the height; `fp`: the finality pair. -/
theorem own_lock_cases (Λ : SigningHistory) (h : Height) (fp : Option FinalityPair) :
    own_lock Λ h fp = Λ.lock h ∨
      ∃ q : FinalityPair, fp = some q ∧ q.hf = h ∧ own_lock Λ h fp = some q.Tf := by
  cases fp with
  | none => left; rfl
  | some q =>
    by_cases hq : q.hf = h
    · right
      refine ⟨q, rfl, hq, ?_⟩
      simp [own_lock, Option.value, hq]
    · left
      simp [own_lock, Option.value, hq]
      rfl

/-- A height pair `height_pair` computes from the source `(h_c, T_c)` that is a vote is at `h_c`
and names `T_c`; a target vote is cast only when the record holds no timeout at `h_c` and the lock
read at `h_c` is unset or `T_c`; a timeout only when the record holds a timeout at `h_c` or the lock
read at `h_c` is unset.

The variables:
- `Λ`: the record; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair;
- `h`, `T`, `τ`: the vote. -/
theorem height_pair_vote_cases {Λ : SigningHistory} {h_c : Height} {T_c : BlockId}
    {fp : Option FinalityPair} {h : Height} {T : BlockId} {τ : Bool}
    (hp : height_pair Λ (some (h_c, T_c)) fp = .vote h T τ) :
    h = h_c ∧ T = T_c ∧
      (τ = false → Λ.timeout h_c = false ∧
        ∀ L : BlockId, own_lock Λ h_c fp = some L → L = T_c) ∧
      (τ = true → Λ.timeout h_c = true ∨ own_lock Λ h_c fp = none) := by
  simp only [height_pair, Id.run, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
    Option.value, Option.get_some, getElem_option, getElem_bool] at hp
  split_ifs at hp <;> obtain ⟨rfl, rfl, rfl⟩ := HeightPair.vote.inj hp <;> simp_all

/-! ## The four writes of `record_attestation` -/

/-- `record_attestation` adds the attestation's content to the contents sent.

The variables:
- `Λ`: the record; `a`: the attestation. -/
theorem record_attestation_sent (Λ : SigningHistory) (a : Attestation V) :
    (record_attestation Λ a).sent = Λ.sent ∪ {a.content} := by
  simp only [record_attestation, Id.run]
  split_ifs <;> rfl

/-- The contents `record_attestation` holds are those of the record and the attestation's.

The variables:
- `Λ`: the record; `a`: the attestation; `c`: a content. -/
theorem mem_record_attestation_sent {Λ : SigningHistory} {a : Attestation V}
    {c : AttestationContent} :
    c ∈ (record_attestation Λ a).sent ↔ c ∈ Λ.sent ∨ c = a.content := by
  rw [record_attestation_sent, Finset.mem_union, Finset.mem_singleton]

/-- `record_attestation` sets the lock at the height of the attestation's finality pair to the
pair's block, and keeps the others.

The variables:
- `Λ`: the record; `a`: the attestation. -/
theorem record_attestation_lock (Λ : SigningHistory) (a : Attestation V) :
    (record_attestation Λ a).lock = match a.finality_pair with
      | some p => Function.update Λ.lock p.hf (some p.Tf)
      | none => Λ.lock := by
  simp only [record_attestation, Id.run]
  cases a.finality_pair <;> simp only [ne_eq, not_true_eq_false, reduceCtorEq,
    not_false_eq_true, dite_true, dite_false, Option.value, Option.get_some] <;> split_ifs <;> rfl

/-- `record_attestation` sets the target at the attestation's height to its block when it is a
target vote and the record holds no target there, and keeps the others.

The variables:
- `Λ`: the record; `a`: the attestation. -/
theorem record_attestation_target (Λ : SigningHistory) (a : Attestation V) :
    (record_attestation Λ a).target =
      if a.τ = false ∧ Λ.target a.h = none then Function.update Λ.target a.h (some a.T)
      else Λ.target := by
  simp only [record_attestation, Id.run, getElem_option]
  split_ifs <;> first | rfl | simp_all

/-- `record_attestation` sets the timeout at the attestation's height when it is a timeout, and
keeps the others.

The variables:
- `Λ`: the record; `a`: the attestation. -/
theorem record_attestation_timeout (Λ : SigningHistory) (a : Attestation V) :
    (record_attestation Λ a).timeout =
      if a.τ = true then Function.update Λ.timeout a.h true else Λ.timeout := by
  simp only [record_attestation, Id.run]
  split_ifs <;> rfl

/-- After `record_attestation`, the target at `h` is `T` exactly when it was, or when the
attestation is a target vote at `h` for `T` and the record held no target at `h`.

The variables:
- `Λ`: the record; `a`: the attestation; `h`: the height; `T`: the block. -/
theorem record_attestation_target_some (Λ : SigningHistory) (a : Attestation V) (h : Height)
    (T : BlockId) :
    (record_attestation Λ a).target h = some T ↔
      Λ.target h = some T ∨ (a.τ = false ∧ h = a.h ∧ Λ.target h = none ∧ T = a.T) := by
  rw [record_attestation_target]
  by_cases hh : h = a.h
  · subst hh
    split_ifs with hc
    · rw [Function.update_self, hc.2]
      simp [hc.1, eq_comm]
    · constructor
      · exact Or.inl
      · rintro (h1 | ⟨h1, -, h2, -⟩)
        · exact h1
        · exact absurd ⟨h1, h2⟩ hc
  · split_ifs
    · rw [Function.update_of_ne hh]
      simp [hh]
    · simp [hh]

/-- After `record_attestation`, the timeout at `h` is set exactly when it was, or when the
attestation is a timeout at `h`.

The variables:
- `Λ`: the record; `a`: the attestation; `h`: the height. -/
theorem record_attestation_timeout_true (Λ : SigningHistory) (a : Attestation V) (h : Height) :
    (record_attestation Λ a).timeout h = true ↔ Λ.timeout h = true ∨ (a.τ = true ∧ h = a.h) := by
  rw [record_attestation_timeout]
  by_cases hh : h = a.h
  · subst hh
    split_ifs with hc
    · simp [hc]
    · simp [hc]
  · split_ifs
    · rw [Function.update_of_ne hh]
      simp [hh]
    · simp [hh]

/-- After `record_attestation`, the lock at `h` is `T` exactly when the attestation's finality pair
is `(h, T)`, or when its finality pair is not at `h` and the record's lock at `h` was `T`.

The variables:
- `Λ`: the record; `a`: the attestation; `h`: the height; `T`: the block. -/
theorem record_attestation_lock_some (Λ : SigningHistory) (a : Attestation V) (h : Height)
    (T : BlockId) :
    (record_attestation Λ a).lock h = some T ↔
      (∃ p : FinalityPair, a.finality_pair = some p ∧ p.hf = h ∧ p.Tf = T) ∨
        ((∀ p : FinalityPair, a.finality_pair = some p → p.hf ≠ h) ∧ Λ.lock h = some T) := by
  rw [record_attestation_lock]
  cases hfp : a.finality_pair with
  | none => simp
  | some p =>
    by_cases hh : p.hf = h
    · subst hh
      simp [eq_comm]
    · simp [Ne.symm hh, hh]

/-- After `record_attestation`, the lock at `h` is unset exactly when the attestation's finality
pair is not at `h` and the record's lock at `h` was unset.

The variables:
- `Λ`: the record; `a`: the attestation; `h`: the height. -/
theorem record_attestation_lock_none (Λ : SigningHistory) (a : Attestation V) (h : Height) :
    (record_attestation Λ a).lock h = none ↔
      (∀ p : FinalityPair, a.finality_pair = some p → p.hf ≠ h) ∧ Λ.lock h = none := by
  rw [record_attestation_lock]
  cases hfp : a.finality_pair with
  | none => simp
  | some p =>
    by_cases hh : p.hf = h
    · subst hh
      simp
    · simp [Ne.symm hh, hh]

/-! ## `create_attestation` -/

/-- `create_attestation` returns the record unchanged and no attestation, or the record with the
attestation written into it, and that attestation: a vote at `h_c` for `T_c` that `height_pair`
computed and `already_sent` allowed, with the finality pair `finality_pair` computed when that is at
a height less than `h_c`, and none otherwise.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height. -/
theorem create_attestation_cases (Λ : SigningHistory) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) :
    create_attestation Λ v h_c T_c h_j J h_F = (Λ, none) ∨
      ∃ (τ : Bool) (fp' : Option FinalityPair),
        height_pair Λ (some (h_c, T_c)) (finality_pair Λ h_j J h_F) = .vote h_c T_c τ ∧
        already_sent Λ h_c T_c τ = false ∧
        (∀ q : FinalityPair, fp' = some q → finality_pair Λ h_j J h_F = some q ∧ q.hf < h_c) ∧
        create_attestation Λ v h_c T_c h_j J h_F =
          (record_attestation Λ ⟨v, h_c, T_c, τ, fp'⟩, some ⟨v, h_c, T_c, τ, fp'⟩) := by
  cases hhp : height_pair Λ (some (h_c, T_c)) (finality_pair Λ h_j J h_F) with
  | empty =>
    left
    simp only [create_attestation, Id.run, hhp]
    rfl
  | vote h T τ =>
    obtain ⟨rfl, rfl, -⟩ := height_pair_vote_cases hhp
    by_cases hs : already_sent Λ h T τ = true
    · left
      simp only [create_attestation, Id.run, hhp, hs]
      rfl
    · right
      have hs' : already_sent Λ h T τ = false := by simpa using hs
      cases hfp : finality_pair Λ h_j J h_F with
      | none =>
        refine ⟨τ, none, rfl, hs', by simp, ?_⟩
        rw [hfp] at hhp
        simp only [create_attestation, Id.run, hhp, hs', hfp, Bool.false_eq_true, ite_false,
          ne_eq, not_true_eq_false, dite_false]
        rfl
      | some q =>
        rw [hfp] at hhp
        by_cases hle : h ≤ q.hf
        · refine ⟨τ, none, rfl, hs', by simp, ?_⟩
          simp only [create_attestation, Id.run, hhp, hs', hfp, Bool.false_eq_true, ite_false,
            ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some, hle]
          rfl
        · refine ⟨τ, some q, rfl, hs', ?_, ?_⟩
          · intro q' hq'
            cases hq'
            exact ⟨rfl, Nat.lt_of_not_le hle⟩
          simp only [create_attestation, Id.run, hhp, hs', hfp, Bool.false_eq_true, ite_false,
            ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some, hle]
          rfl

/-! ## Consistency -/

/-- `record_attestation` keeps a consistent record consistent, when the attestation written is one
the record allows: every content the record holds at its height leaves it a timeout for another
block, a target vote is cast where the record holds no timeout and no lock but its block, a timeout
where the record holds no lock, and its finality pair is at a lesser height where the record holds
no target and no lock but the pair's block, and no timeout.

Why: a new target is written only at a height with no content, a new lock only where every content
names its block and none is a timeout, and the new content is the one each array write records.

The variables:
- `Λ`: the record; `a`: the attestation written. -/
theorem record_attestation_consistent {Λ : SigningHistory} (hΛ : RecordConsistent Λ)
    (a : Attestation V)
    -- every content the record holds at the attestation's height leaves the attestation a timeout
    -- for another block
    (hfree : ∀ b ∈ Λ.sent, b.h = a.h → a.τ = true ∧ b.T ≠ a.T)
    -- a target vote is cast only where the record holds no timeout and no lock but its block
    (htarget : a.τ = false →
      Λ.timeout a.h = false ∧ ∀ L : BlockId, Λ.lock a.h = some L → L = a.T)
    -- a timeout is cast only where the record holds no lock
    (htimeout : a.τ = true → Λ.lock a.h = none)
    -- the finality pair is at a height less than the vote's, where the record holds no target and
    -- no lock but its block, and no timeout
    (hfp : ∀ p : FinalityPair, a.finality_pair = some p → p.hf < a.h ∧
      (∀ T : BlockId, Λ.target p.hf = some T → T = p.Tf) ∧ Λ.timeout p.hf = false ∧
      (∀ T : BlockId, Λ.lock p.hf = some T → T = p.Tf)) :
    RecordConsistent (record_attestation Λ a) where
  oneTarget := by
    intro c hc c' hc' hh hτ hτ'
    rw [mem_record_attestation_sent] at hc hc'
    rcases hc with hc | rfl <;> rcases hc' with hc' | rfl
    · exact hΛ.oneTarget c hc c' hc' hh hτ hτ'
    · exact absurd (hfree c hc hh).1 (by simp [Attestation.content] at hτ'; simp [hτ'])
    · exact absurd (hfree c' hc' hh.symm).1 (by simp [Attestation.content] at hτ; simp [hτ])
    · rfl
  lockKept := by
    intro c hc p hcp c' hc' hh
    rw [mem_record_attestation_sent] at hc hc'
    rcases hc with hc | rfl
    · rcases hc' with hc' | rfl
      · exact hΛ.lockKept c hc p hcp c' hc' hh
      · have hh' : a.h = p.hf := hh
        have hlock : Λ.lock a.h = some p.Tf :=
          (hΛ.lockRec _ _).mpr ⟨c, hc, by rw [hcp, hh']⟩
        cases hτ : a.τ
        · exact ((htarget hτ).2 p.Tf hlock).symm
        · rw [htimeout hτ] at hlock
          exact absurd hlock (by simp)
    · obtain ⟨hlt, htgt, htmo, -⟩ := hfp p hcp
      rcases hc' with hc' | rfl
      · cases hτ' : c'.τ
        · exact htgt c'.T ((hΛ.targetRec _ _).mpr ⟨c', hc', hh, hτ', rfl⟩)
        · have := (hΛ.timeoutRec _).mpr ⟨c', hc', hh, hτ'⟩
          rw [htmo] at this
          exact absurd this (by simp)
      · have hh' : a.h = p.hf := hh
        rw [hh'] at hlt
        exact absurd hlt (Nat.lt_irrefl _)
  targetRec := by
    intro h T
    rw [record_attestation_target_some]
    constructor
    · rintro (hT | ⟨hτ, rfl, -, rfl⟩)
      · obtain ⟨c, hc, hcx⟩ := (hΛ.targetRec h T).mp hT
        exact ⟨c, mem_record_attestation_sent.mpr (Or.inl hc), hcx⟩
      · exact ⟨a.content, mem_record_attestation_sent.mpr (Or.inr rfl), rfl, hτ, rfl⟩
    · rintro ⟨c, hc, hch, hcτ, hcT⟩
      rcases mem_record_attestation_sent.mp hc with hc | rfl
      · exact Or.inl ((hΛ.targetRec h T).mpr ⟨c, hc, hch, hcτ, hcT⟩)
      · right
        refine ⟨hcτ, hch.symm, ?_, hcT.symm⟩
        cases ht : Λ.target h with
        | none => rfl
        | some T' =>
          obtain ⟨b, hb, hbh, -, -⟩ := (hΛ.targetRec h T').mp ht
          have := (hfree b hb (by rw [hbh, ← hch]; rfl)).1
          simp [Attestation.content] at hcτ
          rw [hcτ] at this
          exact absurd this (by simp)
  timeoutRec := by
    intro h
    rw [record_attestation_timeout_true]
    constructor
    · rintro (hT | ⟨hτ, rfl⟩)
      · obtain ⟨c, hc, hcx⟩ := (hΛ.timeoutRec h).mp hT
        exact ⟨c, mem_record_attestation_sent.mpr (Or.inl hc), hcx⟩
      · exact ⟨a.content, mem_record_attestation_sent.mpr (Or.inr rfl), rfl, hτ⟩
    · rintro ⟨c, hc, hch, hcτ⟩
      rcases mem_record_attestation_sent.mp hc with hc | rfl
      · exact Or.inl ((hΛ.timeoutRec h).mpr ⟨c, hc, hch, hcτ⟩)
      · exact Or.inr ⟨hcτ, hch.symm⟩
  lockRec := by
    intro h T
    rw [record_attestation_lock_some]
    constructor
    · rintro (⟨p, hp, rfl, rfl⟩ | ⟨-, hT⟩)
      · exact ⟨a.content, mem_record_attestation_sent.mpr (Or.inr rfl), hp⟩
      · obtain ⟨c, hc, hcx⟩ := (hΛ.lockRec h T).mp hT
        exact ⟨c, mem_record_attestation_sent.mpr (Or.inl hc), hcx⟩
    · rintro ⟨c, hc, hcp⟩
      rcases mem_record_attestation_sent.mp hc with hc | rfl
      · have hT := (hΛ.lockRec h T).mpr ⟨c, hc, hcp⟩
        by_cases hex : ∃ p : FinalityPair, a.finality_pair = some p ∧ p.hf = h
        · obtain ⟨p, hp, rfl⟩ := hex
          exact Or.inl ⟨p, hp, rfl, ((hfp p hp).2.2.2 T hT).symm⟩
        · exact Or.inr ⟨fun p hp hph => hex ⟨p, hp, hph⟩, hT⟩
      · exact Or.inl ⟨⟨h, T⟩, hcp, rfl, rfl⟩
  timeoutUnlocked := by
    intro h hT
    rw [record_attestation_lock_none]
    rcases (record_attestation_timeout_true Λ a h).mp hT with hT | ⟨hτ, rfl⟩
    · refine ⟨fun p hp hph => ?_, hΛ.timeoutUnlocked h hT⟩
      have := (hfp p hp).2.2.1
      rw [hph, hT] at this
      exact absurd this (by simp)
    · exact ⟨fun p hp hph => absurd hph (Nat.ne_of_lt (hfp p hp).1), htimeout hτ⟩

/-- **Lemma 72, the initial record is consistent.** The proof; the audited statement is in
`Statements/Routines/RecordStatements.lean`. -/
theorem lem72_initial_record_consistent : RecordConsistent SigningHistory.initial where
  oneTarget := by simp [SigningHistory.initial]
  lockKept := by simp [SigningHistory.initial]
  targetRec := by simp [SigningHistory.initial]
  timeoutRec := by simp [SigningHistory.initial]
  lockRec := by simp [SigningHistory.initial]
  timeoutUnlocked := by simp [SigningHistory.initial]

/-- **Lemma 72, `create_attestation` keeps the record consistent.** The proof; the audited
statement is in `Statements/Routines/RecordStatements.lean`.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height. -/
theorem lem72_create_attestation_consistent (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (hΛ : RecordConsistent Λ) :
    RecordConsistent (create_attestation Λ v h_c T_c h_j J h_F).1 ∧
      ∀ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a →
        a.content ∈ (create_attestation Λ v h_c T_c h_j J h_F).1.sent := by
  rcases create_attestation_cases Λ v h_c T_c h_j J h_F with heq | ⟨τ, fp', hhp, hs, hfp', heq⟩
  · rw [heq]
    exact ⟨hΛ, fun a ha => absurd ha (by simp)⟩
  · rw [heq]
    refine ⟨?_, fun a ha => ?_⟩
    · obtain ⟨-, -, hfalse, htrue⟩ := height_pair_vote_cases hhp
      -- the lock `height_pair` reads at `h_c` is the record's lock there, when that is set
      have hown : ∀ L : BlockId, Λ.lock h_c = some L →
          own_lock Λ h_c (finality_pair Λ h_j J h_F) = some L := by
        intro L hL
        rcases own_lock_cases Λ h_c (finality_pair Λ h_j J h_F) with ho | ⟨q, hq, hqh, ho⟩
        · rw [ho, hL]
        · obtain ⟨rfl, -, -, -, hlk⟩ := finality_pair_some hq
          rw [ho]
          simp only at hqh
          subst hqh
          rw [hlk L hL]
      refine record_attestation_consistent hΛ _ ?_ ?_ ?_ ?_
      · intro b hb hbh
        simp only [already_sent, decide_eq_false_iff_not, not_exists, not_and] at hs
        have := hs b hb hbh
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, not_or] at this
        exact ⟨by simpa using this.1, this.2⟩
      · intro hτ
        obtain ⟨hto, hL⟩ := hfalse hτ
        exact ⟨hto, fun L hlock => hL L (hown L hlock)⟩
      · intro hτ
        cases hlock : Λ.lock h_c with
        | none => rfl
        | some L =>
          rcases htrue hτ with hto | ho
          · rw [hΛ.timeoutUnlocked h_c hto] at hlock
            exact absurd hlock (by simp)
          · rw [hown L hlock] at ho
            exact absurd ho (by simp)
      · intro p hp
        obtain ⟨hfp, hlt⟩ := hfp' p hp
        obtain ⟨rfl, -, htgt, htmo, hlk⟩ := finality_pair_some hfp
        exact ⟨hlt, htgt, htmo, hlk⟩
    · cases ha
      exact mem_record_attestation_sent.mpr (Or.inr rfl)

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
variable {V : Type}

/-- A timeout `height_pair` computes from the source `(h_c, T_c)` is cast only when the record
holds a timeout at `h_c`, or a target at `h_c` for a block other than `T_c`.

The variables:
- `Λ`: the record; `h_c`, `T_c`: the source's height and root; `fp`: the finality pair;
- `h`, `T`: the vote's height and root. -/
theorem height_pair_timeout {Λ : SigningHistory} {h_c : Height} {T_c : BlockId}
    {fp : Option FinalityPair} {h : Height} {T : BlockId}
    -- `height_pair` computes a timeout
    (hp : height_pair Λ (some (h_c, T_c)) fp = .vote h T true) :
    Λ.timeout h_c = true ∨ ∃ T' : BlockId, Λ.target h_c = some T' ∧ T' ≠ T_c := by
  simp only [height_pair, Id.run, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
    Option.value, Option.get_some, getElem_option, getElem_bool] at hp
  split_ifs at hp with h1 h2 h3 h4
  all_goals first
    | exact Or.inl ‹_›
    | exact absurd (HeightPair.vote.inj hp).2.2 Bool.false_ne_true
    | exact HeightPair.noConfusion hp
    | skip
  right
  cases ht : Λ.target h_c with
  | none => simp [ht] at h3
  | some T' =>
      refine ⟨T', rfl, fun hT => ?_⟩
      simp [ht, hT] at h3

/-- A timeout `create_attestation` builds is at the source's height `h_c`, names `T_c`, and is
built only when the record holds a timeout at `h_c`, or a target at `h_c` for a block other than
`T_c`.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation built. -/
theorem create_attestation_timeout (Λ : SigningHistory) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V)
    -- `create_attestation` builds `a`
    (hSome : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a)
    -- `a` is a timeout
    (hτ : a.τ = true) :
    a.h = h_c ∧ a.T = T_c ∧
      (Λ.timeout h_c = true ∨ ∃ T' : BlockId, Λ.target h_c = some T' ∧ T' ≠ T_c) := by
  rcases create_attestation_cases Λ v h_c T_c h_j J h_F with h0 | ⟨τ, fp', hhp, -, -, h1⟩
  · rw [h0] at hSome; cases hSome
  · rw [h1] at hSome
    have ha : a = ⟨v, h_c, T_c, τ, fp'⟩ := (Option.some.inj hSome).symm
    subst ha
    change τ = true at hτ
    subst hτ
    exact ⟨rfl, rfl, height_pair_timeout hhp⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A lock of the record `create_attestation` returns is a lock of the record it starts from, or is
at the justification height `h_j` it is given: the only lock it writes is that of the finality pair
`finality_pair` computes, which is at `h_j`.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height;
- `h`: the height of the lock; `T`: its block. -/
theorem create_attestation_lock (Λ : SigningHistory) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) (h : Height) (T : BlockId)
    -- the record returned holds the lock `T` at `h`
    (hl : (create_attestation Λ v h_c T_c h_j J h_F).1.lock h = some T) :
    Λ.lock h = some T ∨ h = h_j := by
  rcases GoldilocksCorrectness.Proofs.Routines.create_attestation_cases Λ v h_c T_c h_j J h_F
    with he | ⟨τ, fp', -, -, hfp', he⟩
  · rw [he] at hl
    exact Or.inl hl
  · rw [he] at hl
    rcases (GoldilocksCorrectness.Proofs.Routines.record_attestation_lock_some Λ _ h T).1 hl with
      ⟨p, hp, hph, -⟩ | ⟨-, hl'⟩
    · right
      obtain ⟨hq, -⟩ := hfp' p hp
      obtain ⟨hpq, -⟩ := GoldilocksCorrectness.Proofs.Routines.finality_pair_some hq
      rw [← hph, hpq]
    · exact Or.inl hl'

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `create_attestation` with no attestation answers the record unchanged; with the attestation
`a`, it answers a record whose contents are those of the record and `a`'s, and `a` is of the
validator.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height. -/
theorem create_attestation_record (Λ : SigningHistory) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height) :
    ((create_attestation Λ v h_c T_c h_j J h_F).2 = none →
        (create_attestation Λ v h_c T_c h_j J h_F).1 = Λ) ∧
      ∀ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a →
        a.val_index = v ∧ ∀ b ∈ (create_attestation Λ v h_c T_c h_j J h_F).1.sent,
          b ∈ Λ.sent ∨ b = a.content := by
  rcases create_attestation_cases Λ v h_c T_c h_j J h_F with h | ⟨τ, fp', -, -, -, h⟩
  · rw [h]
    exact ⟨fun _ => rfl, fun a ha => (by cases ha)⟩
  · rw [h]
    refine ⟨fun ha => (by cases ha), fun a ha => ?_⟩
    cases ha
    exact ⟨rfl, fun b hb => mem_record_attestation_sent.1 hb⟩

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The record `create_attestation` returns holds every content the record it starts from holds.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height. -/
theorem create_attestation_sent_subset (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) :
    Λ.sent ⊆ (create_attestation Λ v h_c T_c h_j J h_F).1.sent := by
  rcases create_attestation_cases Λ v h_c T_c h_j J h_F with h | ⟨τ, fp', -, -, -, h⟩
  · rw [h]
  · rw [h]
    exact (record_attestation_sent Λ _).symm ▸ Finset.subset_union_left

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The attestation `create_attestation` builds has its content in the record it returns.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the justification height, the justified root and the finalization height;
- `a`: the attestation built. -/
theorem create_attestation_content_mem {Λ : SigningHistory} {v : V} {h_c : Height}
    {T_c : BlockId} {h_j : Height} {J : BlockId} {h_F : Height} {a : Attestation V}
    -- `create_attestation` builds `a`
    (ha : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a) :
    a.content ∈ (create_attestation Λ v h_c T_c h_j J h_F).1.sent := by
  rcases create_attestation_cases Λ v h_c T_c h_j J h_F with h | ⟨τ, fp', -, -, -, h⟩
  · rw [h] at ha
    cases ha
  · rw [h] at ha ⊢
    cases ha
    exact mem_record_attestation_sent.2 (Or.inr rfl)

end

end

/-- **The initial anti-slashing record, its fields written out.** `SigningHistory.initial` holds no
target, no timeout and no lock at any height, and no attestation content sent.

Read aloud: a validator starts with an empty anti-slashing record.

Added by the record migration, step 1h, for the execution proofs that read the
initial record through the body of `SigningHistory.initial`. -/
theorem signingHistory_initial_eq :
    Goldilocks.SigningHistory.initial =
      ({ target := fun _ => none, timeout := fun _ => false, lock := fun _ => none, sent := ∅ } :
        Goldilocks.SigningHistory) := by
  rfl

end GoldilocksCorrectness.Proofs.Routines
