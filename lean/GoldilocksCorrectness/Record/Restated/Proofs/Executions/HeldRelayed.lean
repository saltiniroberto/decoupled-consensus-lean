module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Invariants
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Routines.WalkEndLemmas
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# What an honest validator holds, it put on the wire itself

The hypothesis `hrelay` of the bridges from the pushed catch-up to the sync fact
(`syncedWithin_of_envFactsSync` and its forms,
`Record/Restated/Proofs/Executions/AsyncDelivery.lean`):
an object of the class `ok` an honest validator holds (`holdsG M`) after a step was put on the wire
by that validator, honest then, at an earlier step, signed by itself.

- `step_attestation_new_sent`: an attestation that enters a validator's held attestations at a step
  was put on the wire by that validator at that step, as an attestation object. A tick that sends a
  block adds none of the block's attestations, since a proposal includes only held ones.
- `held_attestation_sent_alone`: every attestation a validator holds it put on the wire earlier, as
  an attestation object.
- `holdsG_relayed_fg`: `hrelay` for the class `fgObject` (the attestations), whole.
- `holdsG_relayed_block`: the block half of `hrelay` for the class `acObject`, for every block of
  the tree other than the genesis block, which every tree holds from the start and no honest
  validator is required to put on the wire.
- `held_attestation_sent_alone_entry`: `held_attestation_sent_alone` at the step the attestation
  entered the held attestations, which hold it after that step.
- `justifiedHeight_le_succ`, `justifiedHeight_mono_of_le`, `justifiedHeight_mono_of_honest`: a
  validator's justification height does not decrease along the steps of the run.
- `servesMin_relayed_fg`: `hrelay` at the entry step for the minimal selection at `fgObject`: an
  attestation an honest validator serves was put on the wire by it at a step after which it
  already served it.
- `syncedWithin_servesMin_fg_of_envFactsSync`: the pushed catch-up at `fgObject` gives the sync fact
  over `servesMin M S.C` at `fgObject`.
- `syncedWithinOutside_servesMin_fg_of_envFactsOutside`: the same, both suspended on one
  asynchronous period `[b₀, b₁)`.

The selection `servesMin M S.C` serves an attestation `a` held at a justification height at most
`a.h`. The step at which `a` entered the held attestations is the step at which the holder put it
on the wire (`step_attestation_new_sent`); the holder serves `a` after that step, since its
justification height then is at most its later one (`justifiedHeight_mono_of_le`, from the facts
`tick_justifiedHeight_mono`, `receive_justifiedHeight_mono` and the wake's readers), which is at
most `a.h`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open Goldilocks.Sts (Setup)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts EnvFactsSync
  SyncedWithin)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts holdsG servesMin)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- An attestation that enters a validator's held attestations at the step `k` was put on the wire
by that validator at that step, as an attestation object.

Why: the step is the validator's tick or a delivery to it (a wake keeps the attestations held). A
tick adds an attestation it sent, or one included in a block it sent; that block is the node's
proposal (Lemma 19), whose attestations are held ones (`proposal_attestations_eq`, its parent being
in the tree), so the second case adds nothing new. A delivery adds the delivered attestation or one
included in the delivered block, and the wiring re-sends each as an attestation object.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `a`: the attestation.

Read aloud: an attestation a step adds was put on the wire at that step, by itself. -/
theorem step_attestation_new_sent (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {a : Attestation V}
    -- `v` holds `a` after the step
    (ha : a ∈ (x.st (k + 1) v).attestationsHeld)
    -- `v` does not hold `a` before the step
    (hn : a ∉ (x.st k v).attestationsHeld) :
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k := by
  rcases (step_cases_per_step M F) x R E k v with h | ⟨t, n', sent, hl, -, hok, h, hw⟩ |
      ⟨sm, hl, -, h⟩ | ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h] at ha
    exact absurd ha hn
  · rw [h] at ha
    have hin : x.tickInput v t = x.st k v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hok
    rcases F.tk.tick_prov_attestations S.C S.P S.X _ (t : Int) n' sent hok a ha hn with
      h1 | ⟨B, hB, hB'⟩
    · exact hw _ h1
    · -- the block is the node's proposal, whose attestations are held ones
      exfalso
      have hI :=
        ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariant M F) S A x R E k v
          (E.not_mem_corrupted_of_tick hl)).1
      obtain ⟨-, -, -, -, H, votes, support_votes, -, -, hPH, hBeq⟩ :=
        F.tk3.tick_proposal S.C S.P S.X (x.st k v) (t : Int) n' sent B hok hI hB
      obtain ⟨vs, svs, -, hEnd⟩ := hPH
      have hHT : H ∈ (x.st k v).tree :=
        GoldilocksCorrectness.Record.Proofs.Routines.walk_end_mem_T M F S.C S.P S.X _ hI
          (t : Int) H
          ((@GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq V _ M.tieBreak _ _ _ _ _
            hEnd).symm)
          (F.nd.nodeInv_finalized_mem_tree hI) (F.nd.nodeInv_justifiedInTree hI)
      apply hn
      rw [hBeq] at hB'
      change a ∈ M.proposal_attestations (x.st k v) H at hB'
      rw [F.ndAdded.proposal_attestations_eq hI hHT, List.mem_filter] at hB'
      exact hB'.1
  · rw [h] at ha
    refine (step_sent_of_delivery M F) R hl ((F.rcv.mem_relayedObjects_iff _ _).2 ?_)
    rcases F.rcv.receive_new_attestations S.C S.P S.X _ sm.msg a ha hn with hc | ⟨B, hB, hBa⟩
    · exact Or.inl hc.symm
    · exact Or.inr ⟨B, hB, Or.inr ⟨a, hBa, rfl⟩⟩
  · rw [h tRw keepw hlw] at ha
    have ha' : a ∈ M.attestationsHeld (M.wake (x.st k v) (tRw : Int)) := ha
    rw [(F.wk.wake_readers _ _).2.2.2.2.2.2.1] at ha'
    exact absurd ha' hn

/-- Every attestation a validator holds after `k` steps it put on the wire at an earlier step, as
an attestation object, signed by itself.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `a`: the attestation.

Read aloud: every attestation a validator holds it put on the wire itself, by itself. -/
theorem held_attestation_sent_alone (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
        {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {a : Attestation V}
    -- `v` holds `a` after `k` steps
    (ha : a ∈ (x.st k v).attestationsHeld) :
    ∃ i < k, (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i := by
  induction k with
  | zero =>
      rw [(getElem_zero_st M F) x R, F.init.initial_attestationsHeld S.C v] at ha
      exact absurd ha List.not_mem_nil
  | succ k ih =>
      by_cases hk : a ∈ (x.st k v).attestationsHeld
      · obtain ⟨i, hi, hs⟩ := ih hk
        exact ⟨i, by omega, hs⟩
      · exact ⟨k, by omega, (step_attestation_new_sent M F) x R E ha hk⟩

/-- `hrelay` for the class `fgObject`: an attestation an honest validator holds after the step `k`
was put on the wire by that validator, honest then, at an earlier step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `u`: the
  validator; `o`: the object.

Read aloud: every attestation an honest validator holds it put on the wire itself, honest then. -/
theorem holdsG_relayed_fg (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (u : V) (o : NamedObject V)
    -- `o` is an attestation
    (hok : fgObject o)
    -- `u` is outside the adversary set at the time of the step `k`
    (hu : u ∉ A.corrupted k)
    -- `u` holds `o` after `k` steps
    (hh : holdsG M (x.st k u) o) :
    ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ := by
  cases o with
  | block B => exact hok.elim
  | gfVote vote => exact hok.elim
  | attest a =>
      obtain ⟨i, hik, hs⟩ := (held_attestation_sent_alone M F) x R E (k := k) (v := u) hh
      exact ⟨i, hik, hs, not_mem_adv_of_le E hik.le hu⟩

/-- The block half of `hrelay` for the class `acObject`: a block other than the genesis block, of
an honest validator's tree after the step `k`, was put on the wire by that validator, honest then,
at an earlier step.

The genesis block is in every tree from the start and is not one of the objects a tick sends, so no
honest validator need ever put it on the wire: the condition `B ≠ Block.genesis` cannot be dropped.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `u`: the
  validator; `B`: the block.

Read aloud: every block other than the genesis block an honest validator holds it put on the wire
itself, honest then. -/
theorem holdsG_relayed_block (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (u : V) (B : Block V)
    -- `u` is outside the adversary set at the time of the step `k`
    (hu : u ∉ A.corrupted k)
    -- `u` holds `B` after `k` steps
    (hh : holdsG M (x.st k u) (NamedObject.block B))
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, NamedObject.block B⟩ := by
  obtain ⟨i, hik, hs, -⟩ := (tree_block_relayed M F) x R E (k := k) (v := u) hh hg
  exact ⟨i, hik, hs, not_mem_adv_of_le E hik.le hu⟩

/-- Every attestation a validator holds after `k` steps it put on the wire, as an attestation
object signed by itself, at an earlier step after which it holds it: the step at which it entered
the held attestations.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `a`: the attestation; `i`: the step of the send.

Read aloud: every attestation a validator holds it put on the wire itself, at the step after which
it first held it. -/
theorem held_attestation_sent_alone_entry (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {a : Attestation V}
    -- `v` holds `a` after `k` steps
    (ha : a ∈ (x.st k v).attestationsHeld) :
    ∃ i < k, (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i ∧ a ∈ (x.st (i + 1) v).attestationsHeld := by
  induction k with
  | zero =>
      rw [(getElem_zero_st M F) x R, F.init.initial_attestationsHeld S.C v] at ha
      exact absurd ha List.not_mem_nil
  | succ k ih =>
      by_cases hk : a ∈ (x.st k v).attestationsHeld
      · obtain ⟨i, hi, hs, hh⟩ := ih hk
        exact ⟨i, by omega, hs, hh⟩
      · exact ⟨k, by omega, (step_attestation_new_sent M F) x R E ha hk, ha⟩

/-- A step never lowers a validator's justification height: the height after the step `k + 1` is
at least the one after the step `k`.

Why: the step leaves the validator's node state as it was, or is its tick, a delivery to it or its
wake; the tick and the delivery never lower the justification height from a node state satisfying
the node invariant (`tick_justifiedHeight_mono`, `receive_justifiedHeight_mono`; Lemma 11 gives the
invariant and the clock no later than the tick's time), and the wake keeps it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `u`: the
  validator.

Read aloud: a step never lowers the justified height. -/
theorem justifiedHeight_le_succ (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (u : V) :
    M.justifiedHeight (x.st k u) ≤ M.justifiedHeight (x.st (k + 1) u) := by
  -- the clock-free part of Lemma 11 holds for every validator
  have hI := ((lem11_node_invariantCore_of_run M F) S x R k u).1
  rcases (step_cases_per_step M F) x R E k u with h | ⟨t, n', sent, hl, -, hrun, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tR, keep, hlR⟩, -, h⟩
  · rw [h]
  · -- a tick, from the state at its step
    have hin : x.tickInput u t = x.st k u := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hrun
    rw [h]
    exact F.tkAdded.tick_justifiedHeight_mono_of_core S.C S.P S.X _ (t : Int) n' sent hrun hI
  · rw [h]
    exact F.rcvAdded.receive_justifiedHeight_mono_of_core S.C S.P S.X _ sm.msg hI
  · -- a wake keeps the justification height
    obtain ⟨-, -, -, -, -, hJh, -⟩ := F.wk.wake_readers (x.st k u) (tR : Int)
    rw [h tR keep hlR]
    exact le_of_eq hJh.symm

/-- A validator's justification height does not decrease along the steps of the run: from a step
`i` to a later step `k`, the height after `k` is at least the one after `i`.

Why: `justifiedHeight_le_succ` at each step from `i` to `k`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `u`: the validator; `i`,
  `k`: the two steps.

Read aloud: the justified height never decreases along the run. -/
theorem justifiedHeight_mono_of_le (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (u : V) {i k : ℕ} (hik : i ≤ k) :
    M.justifiedHeight (x.st i u) ≤ M.justifiedHeight (x.st k u) :=
  monotone_nat_of_le_succ (f := fun j => M.justifiedHeight (x.st j u))
    (fun j => (justifiedHeight_le_succ M F) x R E j u) hik

/-- The justification height of a validator outside the adversary set at the later step does not
decrease: from a step `i` to a later step `k`, the height after `k` is at least the one after `i`.

Why: `justifiedHeight_mono_of_le`, which holds for every validator.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts.

Read aloud: an honest validator's justified height never decreases. -/
theorem justifiedHeight_mono_of_honest (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) :
    ∀ (u : V) (i k : ℕ), i ≤ k → u ∉ A.corrupted k →
      M.justifiedHeight (x.st i u) ≤ M.justifiedHeight (x.st k u) :=
  fun u _ _ hik _ => (justifiedHeight_mono_of_le M F) x R E u hik

/-- `hrelay` at the entry step for the minimal selection at the class `fgObject`: an attestation an
honest validator serves at `t` after the step `k` was put on the wire by that validator, honest
then, at an earlier step after which it already serves it at `t`.

Why: the send is the step at which the attestation entered the held attestations
(`held_attestation_sent_alone_entry`), which hold it after that step; the justification height
after that step is at most the one after `k` (`justifiedHeight_mono_of_le`), which is at most the
attestation's height.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `u`: the
  validator; `o`: the object; `t`: the time.

Read aloud: every attestation an honest validator serves it put on the wire itself, honest then,
once it served it. -/
theorem servesMin_relayed_fg (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (u : V) (o : NamedObject V) (t : ℕ)
    -- `o` is an attestation
    (hok : fgObject o)
    -- `u` is outside the adversary set at the time of the step `k`
    (hu : u ∉ A.corrupted k)
    -- `u` serves `o` at `t` after `k` steps
    (hh : servesMin M S.C (x.st k u) t o) :
    ∃ i : ℕ, i < k ∧ x.HonestSendAt A i ⟨u, o⟩ ∧ servesMin M S.C (x.st (i + 1) u) t o := by
  cases o with
  | block B => exact hok.elim
  | gfVote vote => exact hok.elim
  | attest a =>
      obtain ⟨i, hik, hs, hin⟩ :=
        (held_attestation_sent_alone_entry M F) x R E (k := k) (v := u) hh.1
      exact ⟨i, hik, ⟨hs, not_mem_adv_of_le E hik.le hu⟩,
        hin, le_trans ((justifiedHeight_mono_of_le M F) x R E u hik) hh.2⟩

/-- The minimal selection serves an attestation whatever the clock value: its clause on an attestation
reads the pool and the justified height only.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the configuration; `n`: the node state; `c`, `c'`: two clock values; `o`: the object, an
  attestation.

Read aloud: a node serves an attestation at one clock value exactly when it serves it at another. -/
theorem servesMin_attest_clock {C : Config} {n : M.N} {c c' : ℕ} {o : NamedObject V}
    -- `o` is an attestation
    (hok : fgObject o)
    -- `n` serves `o` at `c`
    (h : servesMin M C n c o) :
    servesMin M C n c' o := by
  cases o with
  | block B => exact hok.elim
  | gfVote vote => exact hok.elim
  | attest a => exact h

/-- The pushed catch-up at the class `fgObject` gives the sync fact over the minimal selection at
`fgObject`: `syncedWithin_servesMin_of_envFactsSync` with `hrelay` from `servesMin_relayed_fg`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `hΔ`: `1 ≤ Δ`; `E`:
  the synchronous promises at `fgObject`; `E'`: the environment's facts at `Δ S` and `acObject`,
  which the relay facts read.

Read aloud: the pushed catch-up gives the sync fact for the attestations a holder serves. -/
theorem syncedWithin_servesMin_fg_of_envFactsSync (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {Δ' Δw GST : ℕ}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsSync A x ΔClockAhead ΔClockBehind Δ' Δw ΔRedeliver GST (releaseOf M S.C) fgObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔA : (Δ' : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ' Δw ≤ Δs)
    {GSTe : ℕ}
    {ΔNet : ℕ} (E' : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) :
    SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs GST :=
  (syncedWithin_servesMin_of_envFactsSync M) R E hΔA hΔw
    (fun k u o hok hu hh => by
      obtain ⟨i, hik, hs, hin⟩ := (servesMin_relayed_fg M F) x R E' k u o (x.clockValue k u) hok hu hh
      exact ⟨i, hik, hs, (servesMin_attest_clock M F) hok hin⟩)

/-- The pushed catch-up at the class `fgObject`, suspended on the asynchronous period `[b₀, b₁)`,
gives the sync fact over the minimal selection at `fgObject` suspended on that period:
`syncedWithinOutside_of_envFactsOutside` with `hrelay` from `servesMin_relayed_fg`. The relay facts
read no delivery promise, so `E'` is any instance of the environment's facts at `acObject`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `hΔ`: `1 ≤ Δ'`; `E`:
  the promises at `fgObject` suspended on `[b₀, b₁)`; `E'`: an instance of the environment's facts
  at `acObject`, with any deadlines, which the relay facts read.

Read aloud: the suspended pushed catch-up gives the suspended sync fact for the attestations a
holder serves. -/
theorem syncedWithinOutside_servesMin_fg_of_envFactsOutside (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {Δ' Δw GST b₀ b₁ : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ' Δw ΔRedeliver GST release fgObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁)
    {Δs : ℕ} (hΔA : (Δ' : ℝ) + ΔClockAhead ≤ Δs) (hΔw : max Δ' Δw ≤ Δs)
    {deadline}
    (E' : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) :
    GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinOutside A x (servesMin M S.C)
      fgObject release ΔRedeliver Δs GST b₀ b₁ :=
  (GoldilocksCorrectness.Record.Proofs.Executions.syncedWithinOutside_of_envFactsOutside M) R E hΔA hΔw
    (fun k u o hok hu hh => by
      obtain ⟨i, hik, hs, hin⟩ := (servesMin_relayed_fg M F) x R E' k u o (x.clockValue k u) hok hu hh
      exact ⟨i, hik, hs, (servesMin_attest_clock M F) hok hin⟩)

end GoldilocksCorrectness.Record.Proofs.Executions
