module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Lemma19
public import GoldilocksCorrectness.Proofs.Executions.ProposalPropagation
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeSends
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma22, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma22.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 22a, an honest proposer holds its own
proposal by the vote time of its slot (the field `tick_proposal` of `F.tk3`), and Lemma 22, the
proposal reaches every validator awake and honest for the next delay. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

/-! ## The relation between a routine's answer and what it sends -/

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem voteTime_eq)

/-! ## The routine level -/

/-! ## Along an execution -/

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 22a, an honest proposer holds its own proposal.** The proof; the audited statement is
in `Statements/Executions/ProposalPropagationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer.



Read aloud: an honest proposer holds the block its tick at the start of slot `s + 1` sends, right
after that tick. -/
theorem lem22a_proposer_holds_own_proposal (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s i : ℕ) (B : Block V) (p : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    -- the root of `B` is new to `p`
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    -- `p` holds `B`'s parent, and its finalized block is compatible with `B`
    (hParentHeld : B.parent ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree)
    (hF : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.compatible B = true) :
    B ∈ (x.st (i + 1) p).tree := by
  -- step 0: the times; the slot of `t₁` is `s + 1`, the slot of `t₁ − 1` is `s` (the spec's slot
  -- of a natural-number time is the model's, `U`)
  have hΔ := one_le_Δ S
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _) (by omega)
  have hslot₀ : S.C.slot ((M.slotStart S.C (s + 1) - 1 : ℕ) : Int) = s :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hT1 : 1 ≤ M.slotStart S.C (s + 1) := by omega
  -- step 1: `p`'s tick at `t₁` answered and sent `B`; it starts from `p`'s state at the step `i`
  obtain ⟨-, n', sent, hrun, hBs, hst, -⟩ := (tick_send_step_outcome_per_step M F R E) hl hsent
  have hti : x.tickInput p (M.slotStart S.C (s + 1)) = x.st i p := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hpv : p ∉ A.corrupted i :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active i p _ hl).1
  have hInv : M.nodeInv S.C S.P S.X (x.tickInput p (M.slotStart S.C (s + 1))) := by
    rw [hti]
    exact ((lem11_node_invariant M F S A x R E i p) hpv).1
  -- step 2: the tick's input state has `p`'s readers before `t₁` (only `p`'s wake comes between,
  -- and it changes none of them)
  -- `p`'s proposing tick read a present `awakeSince` (the field `tick_proposal` of `F.tk3`), so no
  -- wake step of `p` comes before it at `t₁`
  obtain ⟨-, -, -, ⟨τ, hτ, -⟩, -⟩ := F.tk3.tick_proposal S.C S.P S.X _ _ n' sent B hrun hInv hBs
  -- the finalized block is `B`, an ancestor of `B`, or a descendant of `B`
  rcases (compatible_iff _ _).1 hF with hF | hBF
  rotate_left
  · -- `B` is an ancestor of `p`'s finalized block: `p`'s tree already holds it, and the tree only
    -- grows
    have hBT : B ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree :=
      (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p _ B
        (F.nd.nodeInv_finalized_mem_tree hInv) hBF
    rw [hti] at hBT
    exact (mem_T_mono M F) x R E p (Nat.le_succ i) hBT
  -- step 3: the parent's slot is at most `s`, the slot of `t₁ − 1`
  -- (the parent is in `p`'s tree at the tick step, whose clock value is less than `t₁`: the tick reads
  -- a present `awakeSince`)
  have hps : B.parent.slot < S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) := by
    have hPi : B.parent ∈ (x.st i p).tree := by rw [← hti]; exact hParentHeld
    have h1 := (slot_le_clockValue_of_mem_tree M F) R E hpv hPi
    have hτi : (x.st i p).awakeSince = some τ := by rw [← hti]; exact hτ
    have h2 := (clockValue_lt_of_tick_awakeSince_some M F) R E hl (by omega) hτi
    have h2' : x.clockValue i p ≤ M.slotStart S.C (s + 1) - 1 := by omega
    have h3 : S.C.slot ((x.clockValue i p : ℕ) : Int) ≤ s := by
      rw [← hslot₀]
      exact GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast h2')
    rw [hslot₁]
    exact Nat.lt_succ_of_le (h1.trans h3)
  -- step 4: the tick leaves `B` in the tree (the field `tick_proposal_mem_tree` of `F.tk`)
  have hmem : B ∈ n'.tree := by
    refine F.tk.tick_proposal_mem_tree S.C S.P S.X _ _ n' sent B hrun hBs ?_ ?_ ?_ ?_ ?_ hps
    · intro vote hvote
      change vote ∈ M.votesHeld _ _ at hvote
      exact (F.nd.nodeInv_poolKeyed hInv) _ vote hvote
    · exact hRootNew
    · -- the attestations of `p`'s pool are well formed: the node invariant
      exact F.nd.nodeInv_poolAttestationsWellFormed hInv
    · exact hParentHeld
    · exact hF
  -- step 5: the tree the tick leaves is `x.st (i + 1) p`'s
  rw [hst]
  exact hmem

/-- **Kit theorem, the delivery of an honest proposal to the next slot's voter, for any deadline**
(the proof of Lemma 22 and of its `UpTo` form). `p` ticks to the start of slot `s + 1` at `i`, puts its block
`B` on the wire and holds it; `w` ticks to the vote time of slot `s + 1` at `kR` and is active from the
earliest real time of a tick to the start of slot `s + 1` up to `kR`; the deadline of `p`'s send, plus
`ΔClockAhead`, is at most the vote time. Then `B` is in `w`'s tree on the state `kR` starts from, when
`w`'s finalized block there is compatible with `B`: the delivery promise delivers `B` before `kR` to a `w` whose clock has reached the start of `B`'s
slot, its re-delivery premise discharged by `w`'s tick to the start of slot `s + 1`, and `mem_tree_of_admitted_delivery` admits it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `A`: the activity; `x`: the execution; `R`: the run's facts; `E`: the environment's
  facts with the deadline `deadline`; `s`: the slot before the proposal's; `i`: `p`'s tick; `B`: the
  block; `p`: the proposer; `w`: the voter; `d`: the deadline of `p`'s send.

Read aloud: an honest proposal whose delivery deadline leaves `ΔClockAhead` before the vote time of its
slot is in the tree of every validator active from its slot's start up to its tick to that vote time,
whose finalized block there is compatible with it. -/
theorem proposal_held_by_voter_of_deadline (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s i : ℕ) (B : Block V) (p w : V)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, (M.slotStart S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kR → w ∈ A.active j)
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hBp : B ∈ (x.st (i + 1) p).tree)
    -- the deadline `d` of `p`'s send, plus `ΔClockAhead`, is at most the vote time of slot `s + 1`
    {d : ℝ} (hdl : deadline ⟨p, NamedObject.block B⟩ (x.time (i + 1)) = some d)
    (hd : d + ΔClockAhead ≤ (M.voteTime S.C (s + 1) : ℝ))
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
  classical
  obtain ⟨kR, hkR, hwin⟩ := hw
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (0 : ℝ) ≤ Δ S := Nat.cast_nonneg _
  -- the slot layout: `voteTime (s + 1) = slotStart (s + 1) + Δ`, `voteTime s ≤ slotStart (s + 1)`
  have hss : ∀ n : ℕ, M.slotStart S.C n = 4 * Δ S * n := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
  have hvt : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s ≤ M.slotStart S.C (s + 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s, hss, hss,
      Nat.mul_add, Nat.mul_one]
    omega
  have hvtR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = (M.slotStart S.C (s + 1) : ℝ) + Δ S := by
    rw [hvt]; push_cast; ring
  have hT1 : 1 ≤ M.slotStart S.C (s + 1) := by
    rw [hss]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hΔ) (Nat.succ_pos s)
  -- the real times of `p`'s tick `i` and of `w`'s tick `kR`
  obtain ⟨⟨hTi0, hTi⟩, hTi10, hTi1⟩ := (time_of_lbl_tick M) x R E hl
  have hkRt := (E.tick_active kR w _ hkR).2.1
  rw [hvtR] at hkRt
  have hik : i < kR := by
    by_contra hc
    have := htime (show kR ≤ i by omega)
    linarith
  have hpi : p ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hpi1 : p ∉ A.corrupted (i + 1) := E.not_mem_corrupted_succ_of_tick hl
  have hwkR : w ∉ A.corrupted kR :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active kR w _ hkR).1
  -- `w` is active at every step from `i + 1` to `kR`
  have hwin' : ∀ j : ℕ, i + 1 ≤ j → j ≤ kR → w ∈ A.active j := fun j h1 h2 =>
    hwin j (le_trans hTi10 (htime h1)) h2
  -- the deadline of `p`'s send is at most the time of `kR`
  have hdk : d ≤ x.time kR := by
    have := (E.tick_active kR w _ hkR).2.1
    linarith
  -- `B`'s slot is at most `s + 1`: `p` holds it right after its tick to the start of slot `s + 1`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hslot₁ : S.C.slot ((M.slotStart S.C (s + 1) : ℕ) : Int) = s + 1 :=
    hsl _ ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (le_refl _)
      (by rw [hss, hss]; exact (Nat.mul_lt_mul_left (Nat.mul_pos (by norm_num) hΔ)).2 (by omega))
  have hBs : B.slot ≤ s + 1 := by
    have h := (slot_le_clockValue_of_mem_tree M F) R E hpi1 hBp
    rw [x.clockValue_succ_of_tick hl, hslot₁] at h
    exact h
  have hrs : M.slotStart S.C B.slot ≤ M.slotStart S.C (s + 1) := by
    rw [hss, hss]; exact Nat.mul_le_mul_left _ hBs
  -- `w` ticks to the start of slot `s + 1` at a step `k₂`, in that clock value's window, before `kR`
  obtain ⟨k₂, hk₂, hk₂0, hk₂1⟩ := E.tick_of_active (M.slotStart S.C (s + 1)) hT1 w fun j h1 h2 => by
    refine hwin j h1 ?_
    by_contra hc
    have := htime (show kR ≤ j by omega)
    linarith
  -- the re-delivery premise: a delivery that found `w` not reacted to `B`'s release clock value is
  -- before `k₂`, so `w`'s first tick at a clock value at least it is `k₂` or earlier
  have hprem : ∀ (r j₀ k₁ t₁ : ℕ),
      releaseOf M S.C (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)).msg = some r →
      i < j₀ → x.lbl j₀ = Event.deliver w ⟨p, NamedObject.block B⟩ → ¬ x.ReactedAtLeast j₀ w r →
      j₀ < k₁ → k₁ ≤ kR → x.lbl k₁ = Event.tick w t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick w t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kR := by
    intro r j₀ k₁ t₁ hrel _ _ hnr hjk₁ _ hlk₁ _ hfirst
    have hr' : M.slotStart S.C B.slot = r := Option.some.inj hrel
    subst hr'
    have hj₀k₂ : j₀ < k₂ := by
      by_contra hc
      exact hnr ⟨k₂, by omega, M.slotStart S.C (s + 1), hrs, Or.inl hk₂⟩
    have hk₁k₂ : k₁ ≤ k₂ := by
      by_contra hc
      have := hfirst k₂ _ hj₀k₂ (by omega) hk₂
      omega
    have h1 := htime hk₁k₂
    rw [R.time_keep k₁ (by rw [hlk₁]; exact nofun)]
    linarith
  -- the delivery of `B` to `w` before `kR`, which found `w` reacted to the start of `B`'s slot
  obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered i kR w ⟨p, NamedObject.block B⟩ _ _ ⟨hsent, hpi⟩
    (show acObject (NamedObject.block B) from trivial) hkR hik hwin' hdl hdk hprem
  have hreact : x.ReactedAtLeast j w (M.slotStart S.C B.slot) :=
    hadm _ rfl (hrs.trans (by rw [hvt]; omega))
  have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st kR w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hkR]
  rw [hti] at hF ⊢
  have hTj : x.time j ≤ x.time (x.tickStep w (M.voteTime S.C (s + 1))) := by
    rw [(tickStep_eq_of_lbl M) x E hkR]
    exact htime hjk.le
  exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hpi1
    (by rw [(tickStep_eq_of_lbl M) x E hkR]; exact htime hik) hBp hlj hTj hreact hjk hwkR hF

/-- **Lemma 22, an honest proposal reaches the next slot's voter.** The proof; the audited
statement is in `Statements/Executions/ProposalPropagationStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer;
  `w`: the voter of slot `s + 1`.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`, the step the
delivery of `B` to `w` comes before. The proposer's honesty is read at its own tick
`i` (`tick_active`); no honesty of `p` at a real time is asked.

Read aloud: after `GST`, an honest proposal of slot `s + 1` is held by the vote time of slot `s + 1`
by every validator awake and honest from the slot's start to its vote time whose finalized block is
compatible with it. -/
theorem lem22_proposal_held_by_voter (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s i : ℕ) (B : Block V) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ M.voteTime S.C s)
    -- `w` ticks to the vote time of slot `s + 1` at a step `kR` and is active after every step from the first one
    -- whose time is `ΔClockAhead` before the start of slot `s + 1` up to `kR` (, T-K1)
    (hw : ∃ kR : ℕ, x.lbl kR = Event.tick w (M.voteTime S.C (s + 1)) ∧
      ∀ j : ℕ, (M.slotStart S.C (s + 1) : ℝ) - ΔClockAhead ≤ x.time j → j ≤ kR → w ∈ A.active j)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, put `B` on the wire, and left
    -- `p` holding `B`
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hBp : B ∈ (x.st (i + 1) p).tree)
    -- `w`'s finalized block before its vote is compatible with `B`
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
  -- the deadline `max (x.time (i + 1)) GST + ΔNet` leaves `ΔClockAhead` before the vote time: `p`'s
  -- tick is at most `ΔClockBehind` after the slot's start, `GST` is at most the slot's start, and `hNet`
  have hvt : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s ≤ M.slotStart S.C (s + 1) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s,
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
    have := one_le_Δ S
    omega
  have hGSTR : (GST : ℝ) ≤ M.slotStart S.C (s + 1) := by exact_mod_cast hGST.trans hv₁
  have hvtR : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = (M.slotStart S.C (s + 1) : ℝ) + Δ S := by
    rw [hvt]; push_cast; ring
  have hTi1 := ((time_of_lbl_tick M) x R E hl).2.2
  have hB0 := E.behind_nonneg
  have hmax : max (x.time (i + 1)) (GST : ℝ) ≤ (M.slotStart S.C (s + 1) : ℝ) + ΔClockBehind :=
    max_le hTi1 (by linarith)
  exact (proposal_held_by_voter_of_deadline M F U) S A x R s i B p w E hSkew hRedeliver hRoots hParent hw hl
    hsent hBp rfl (by rw [hvtR]; linarith) hF

end GoldilocksCorrectness.Record.Proofs.Executions

