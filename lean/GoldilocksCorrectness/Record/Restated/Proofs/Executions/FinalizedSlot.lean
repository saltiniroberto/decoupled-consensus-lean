module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodCertificateEntry
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.FinalizedFromChain
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.SentUnforgeable
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Sleepy

@[expose] public section

/-!

For `v` outside the adversary set after `k` steps, `B` in its tree, its clock value after `k`
steps at most the support cutoff of slot `B.slot + 1`, fewer than a quorum in the adversary set
up to the time after `k` steps, and roots naming blocks until then: `v`'s finalized block after
`k` steps is not a strict descendant of `B` (when `B` is an ancestor of it, it is `B`).

Read aloud: a validator's finalized block never runs ahead of a block of the slot its clock is in.
-/

open GoldilocksCorrectness.Statements.Network
set_option autoImplicit false
set_option linter.unusedSectionVars false
open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn TreeClosed)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject author)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_genesis_iff
  compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **An honest attestation naming a block is never included on that block's chain.** When `u`,
outside the adversary set up to the time after `k` steps, is the validator of an attestation `a`
whose target root is the root of a block `T`, `a` is included in a block `Y` that is `T` or an
ancestor of `T`, `Y` is held by `w` outside the adversary set after `k` steps, and `T` is held by
`w` after `k` steps, with roots naming blocks until the time after `k` steps: contradiction.

Why: take the first step `m₀` at which `u`'s signed attestation is on the wire (it is, since `Y`
was put on the wire by `w` and unforgeability puts `a` under `u`'s signature by then). The tick
`k' < m₀` that put it there attested the entry block of its source's chain state, held at `k'`,
whose root is `a.T = T.root`, so that entry is `T` (roots name blocks), so `Y`, an ancestor of
`T` or `T`, is held by `u` at `k'`, so `u` put `Y` on the wire at a step `i' < k'`, and by
unforgeability `a` under `u`'s signature was on the wire after `i' + 1 ≤ k' < m₀` steps.

Read aloud: nobody can include an honest attestation for a block in that block's own chain, since
the attester already held the block when it attested. -/
theorem no_honest_attestation_on_own_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (w u : V) (T Y : Block V) (a : Attestation V)
    (hRoots : RootsNameBlocksUntil M A x (x.time k))
    (hw : w ∉ A.corrupted k)
    (hu : A.HonestThroughTime x (x.time k) u)
    (hT : T ∈ (x.st k w).tree)
    (hYT : Y.AncestorEq T)
    (hau : a.val_index = u) (haT : a.T = T.root)
    (haY : a ∈ Y.attestations) : False := by
  classical
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  have huK : x.HonestThrough A k u := fun i hi => hu i (htime hi)
  have hY : Y ∈ (x.st k w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k w T Y
      hT hYT
  have hYg : Y ≠ Block.genesis := by
    rintro rfl
    exact absurd haY List.not_mem_nil
  have hauth : author (NamedObject.attest a) = some u := by
    simp [author, hau]
  -- `u`'s signed attestation is on the wire after `i + 1 ≤ k` steps
  obtain ⟨i, hik, hsendY, -, -⟩ := (tree_block_relayed M F) x R E hY hYg
  have hsentK : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) :=
    (sent_unforgeable M F) R E (i + 1) ⟨w, .block Y⟩ (.attest a) u
      ((mem_sent_of_mem_sub M F) x hsendY) (Or.inr (Or.inr ⟨a, haY, rfl⟩)) hauth
      (Activity.HonestThroughStep.mono (by omega) huK)
  -- the first step at which it is on the wire
  have hex : ∃ m : ℕ, (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent m :=
    ⟨i + 1, hsentK⟩
  set m₀ := Nat.find hex with hm₀def
  have hm₀ : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent m₀ := Nat.find_spec hex
  have hmin : ∀ n, n < m₀ → (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent n :=
    fun n hn => Nat.find_min hex hn
  have hm₀k : m₀ ≤ i + 1 := Nat.find_min' hex hsentK
  -- the tick of `u` that put it there
  obtain ⟨k', hk'm, t', hl, hsent'⟩ := (authored_from_own_tick M F) x R E hauth hm₀
    (Activity.HonestThroughStep.mono (by omega) huK)
  -- that tick attested the entry of its source's chain state, held at `k'`
  obtain ⟨sₐ, source, C, -, -, -, hsrcT, -, -, -, haT'⟩ :=
    (attest_tick_update_source M F U) S A x R k' t' u a E hl hsent'
  obtain ⟨-, -, hE3⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.isEntry_T_h M F) S.C source
  have hET : (M.chainStateOf S.C source).T_h ∈ (x.st k' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k' u
      source _ hsrcT hE3
  have hk'k : k' ≤ k := by omega
  have hEq : (M.chainStateOf S.C source).T_h = T := hRoots _ T
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k') (v := u) (huK k' hk'k) (htime hk'k) hET) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := w) hw le_rfl hT) (haT'.symm.trans haT)
  rw [hEq] at hET
  -- so `Y` is held by `u` at `k'`, and `u` put it on the wire before `k'`
  have hYu : Y ∈ (x.st k' u).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k' u T Y
      hET hYT
  obtain ⟨i', hi'k', hsendY', -, -⟩ := (tree_block_relayed M F) x R E hYu hYg
  have hsent'' : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i' + 1) :=
    (sent_unforgeable M F) R E (i' + 1) ⟨u, .block Y⟩ (.attest a) u
      ((mem_sent_of_mem_sub M F) x hsendY') (Or.inr (Or.inr ⟨a, haY, rfl⟩)) hauth
      (Activity.HonestThroughStep.mono (by omega) huK)
  exact hmin (i' + 1) (by omega) hsent''

/--

Why: the finalized block `Fb` is the finalized block of the chain state of a held block `D`
(`finalizedFromChain_of_exec`). If `Fb ≠ B`, `Fb` is not the genesis block, so `D`'s chain state
finalized at a height at least `1`, and Lemma 66 gives a justification certificate for `Fb` on
`D`'s chain, with `Fb` an ancestor of `D` or `D`. Slots: `B.slot < Fb.slot` (a strict ancestor has a
smaller slot in a held tree), `D.slot ≤ B.slot + 1` (a held block's slot is at most the slot of the
holder's clock value), so `Fb = D`. The certificate has a member `u` outside the adversary set up
to the time after `k` steps, whose attestation names `Fb`'s root and is included on `Fb`'s chain:
`no_honest_attestation_on_own_chain`.

Read aloud: a validator's finalized block never runs ahead of a block of the slot its clock is in.
-/
theorem finalized_eq_of_ancestorEq_of_clock_le (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (v : V) (B : Block V)
    -- fewer than a quorum have been in the adversary set up to the time after `k` steps
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time k))
    -- roots name blocks among the blocks honest validators hold by that time
    (hRoots : RootsNameBlocksUntil M A x (x.time k))
    -- `v` is outside the adversary set after `k` steps
    (hv : v ∉ A.corrupted k)
    -- `v`'s clock value after `k` steps is at most the support cutoff of slot `B.slot + 1`
    (hclk : x.clockValue k v ≤ M.supportCutoff S.C (B.slot + 1))
    -- `B` is `v`'s finalized block after `k` steps or an ancestor of it
    (hBF : B.AncestorEq (x.st k v).finalized) :
    (x.st k v).finalized = B := by
  classical
  by_contra hne
  have htime : Monotone x.time := fun _ _ h => (time_mono M) x R h
  obtain ⟨D, hD, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E k v
  -- the finalized block is not the genesis block
  have hFg : (x.st k v).finalized ≠ Block.genesis := by
    intro hg
    rw [hg] at hBF hne
    exact hne ((ancestorEq_genesis_iff B).1 hBF).symm
  have h0 : (M.chainStateOf S.C D).h_F ≠ 0 := by
    intro h0
    apply hFg
    rw [hF]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D h0
  obtain ⟨hJ, -, hFD, -⟩ :=
    ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
      (Nat.one_le_iff_ne_zero.mpr h0)
  rw [← hF] at hJ hFD
  -- the finalized block is held, and the tree is closed under parents with earlier slots
  have hFT : (x.st k v).finalized ∈ (x.st k v).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E k v D _
      hD hFD
  have hTC : TreeClosed M S.P S.X (x.st k v) :=
    F.nd.nodeInv_treeClosed (lem11_node_invariant M F S A x R E k v hv).1
  -- slots: `B.slot < Fb.slot`, and `D.slot ≤ B.slot + 1`
  have hBlt : B.slot < (x.st k v).finalized.slot :=
    (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC hFT hBF (fun h => hne h.symm)
  have hDs : D.slot ≤ B.slot + 1 := by
    have h1 := (slot_le_clockValue_of_mem_tree M F) R E hv hD
    have h2 : S.C.slot ((x.clockValue k v : ℕ) : Int) ≤
        S.C.slot ((M.supportCutoff S.C (B.slot + 1) : ℕ) : Int) :=
      GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hclk)
    -- the spec's slot of a natural-number time is the layout's (`U`)
    have hsl : ∀ t' : ℕ, S.C.slot ((t' : ℕ) : Int) = M.slot S.C t' := fun t' => by
      rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
        (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    rw [hsl, hsl, ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout
      F.sched) S B.slot).1] at h2
    rw [hsl] at h1
    exact le_trans h1 h2
  -- so the finalized block is `D` itself
  have hFeqD : (x.st k v).finalized = D := by
    by_contra hneD
    have hlt := (slot_lt_of_ancestorEq_of_treeClosed_node M F) hTC hD hFD hneD
    have hle : (x.st k v).finalized.slot ≤ B.slot := Nat.lt_succ_iff.1 (lt_of_lt_of_le hlt hDs)
    exact absurd hBlt (not_lt.2 hle)
  rw [← hFeqD] at hJ hD
  -- the certificate has a member outside the adversary set up to the time after `k` steps
  obtain ⟨X, hXF, Q, hqA, hQ⟩ := hJ
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hqA
  obtain ⟨u, hu, hhonM⟩ : ∃ u ∈ Q, A.HonestThroughTime x (x.time k) u := by
    by_contra hno
    have hall : ∀ v ∈ Q, ∃ i : ℕ, x.time i ≤ x.time k ∧ v ∈ A.corrupted i := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun i hi ha => hn ⟨i, hi, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  obtain ⟨a, hau, -, haT, -, hon⟩ := hQ u hu
  -- its attestation is included in a block of the finalized block's chain
  obtain ⟨Y, hYF, -, haY⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.exists_of_on_chain M F) a _
    ((GoldilocksCorrectness.Record.Proofs.Routines.on_chain_mono M F) a hXF hon)
  exact (no_honest_attestation_on_own_chain M F U) S A x R E k v u _ Y a hRoots hv hhonM hFT hYF
    hau haT haY

/-- **The base's form: compatibility and the clock bound give the ancestor relation.** For `v`
outside the adversary set after `k` steps, its clock value after `k` steps at most the support
cutoff of slot `B.slot + 1`, fewer than a quorum in the adversary set up to the time after `k`
steps and roots naming blocks until then: when `v`'s finalized block after `k` steps is compatible
with `B`, it is `B` or an ancestor of `B` (`hFinAr`'s row).

Read aloud: a finalized block compatible with a block of the slot the clock is in is that block
or an ancestor of it. -/
theorem finalized_ancestorEq_of_compatible_of_clock_le (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (v : V) (B : Block V)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time k))
    (hRoots : RootsNameBlocksUntil M A x (x.time k))
    (hv : v ∉ A.corrupted k)
    (hclk : x.clockValue k v ≤ M.supportCutoff S.C (B.slot + 1))
    (hcomp : (x.st k v).finalized.compatible B = true) :
    (x.st k v).finalized.AncestorEq B := by
  rcases (compatible_iff _ _).1 hcomp with h | h
  · exact h
  · rw [(finalized_eq_of_ancestorEq_of_clock_le M F U Fx) S A x R E k v B hAdvQ hRoots hv hclk h]
    exact ancestorEq_refl B

end GoldilocksCorrectness.Record.Proofs.Executions
