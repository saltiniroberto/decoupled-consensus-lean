module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestAccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableStatementsChains
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.CertificateStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalViabilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Record
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.HeightCacheAttained
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseFrame, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PhaseFrame.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the frame facts of the phase, Lemma 68's
honest corollary (Lemma 89a), the greatest chain-state height of an honest validator keeps up with
the honest attestations (Lemma 89b), the threshold (Lemma 89h) and the height bound from the old
attestations, read with the greatest chain-state height `hMax M S.C n` of the node's tree in place
of the cache `h_max`. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_mono slot_mono_int
  supportCutoff_eq voteTime_eq Δ_cast)

open GoldilocksCorrectness.Proofs.Routines (block_admissible_of mem_T_receive_block)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (hMax)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  create_attestation_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The kit -/

omit [RootOrder] in
/-- When fewer than a third of the validators have been in the adversary set up to `t'`, the same
holds up to every `t ≤ t'`.

The variables:
- `M`: the model; `F`: its facts;
- `Sched`: the schedule; `t ≤ t'`: the two times.

Read aloud: when fewer than a third of the validators have been in the adversary set up to `t'`, the
same holds up to every `t ≤ t'`. -/
theorem adversaryFewerThanThirdUntil_of_le {Msg N : Type} {x : Trace V Msg N} {t t' : ℕ} (htt : t ≤ t')
    (h : A.AdversaryFewerThanThirdUntil x (validator_count V) t') :
    A.AdversaryFewerThanThirdUntil x (validator_count V) t :=
  fun A hA => h A (fun v hv =>
    let ⟨t'', h1, h2⟩ := hA v hv
    ⟨t'', le_trans h1 (by exact_mod_cast htt), h2⟩)

/-- A tick that puts an attestation on the wire is at a time at least `1`.

Why: the tick sends an attestation only at the action time of the round of its slot (Lemma 49),
`6 * Δ` after the round's opening time, which is at least `0`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `t`: the
  reading of the tick; `u`: the sender; `a`: the attestation.

Read aloud: an attestation is never sent by a tick at time `0`. -/
theorem one_le_of_tick_attestation (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {u : V}
    {a : Attestation V}
    -- the step `i` is `u`'s tick at `t`
    (hl : x.lbl i = Event.tick u t)
    -- the step `i` put `u`'s attestation `a` on the wire
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    1 ≤ t := by
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput u t) := by
    rw [show x.tickInput u t = x.st i u by
      unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]]
    exact (lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick (by assumption))).1
  -- Lemma 49 over the record: the tick ran at the action time of its round
  obtain ⟨hAct, -⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _
    n' _ sent a hrun hInvT ha
  have hΔ := S.C.Δ_pos
  have h0 : ∀ s : ℕ, (0 : Int) ≤ S.C.t_ s := fun s => by rw [t_eq_mul]; positivity
  have h1 := h0 (S.C.round (S.C.slot (t : Int)) * S.C.R)
  unfold Goldilocks.Config.a_ Goldilocks.Config.T_ at hAct
  have h2 : (((t : ℕ) : Int) : Int) = S.C.t_ (S.C.round (S.C.slot (t : Int)) * S.C.R) + 6 * S.C.Δ :=
    hAct
  have h3 : (0 : Int) < S.C.Δ := hΔ
  omega

/-- The attestation a tick sends has the chain-state height of a block of the sender's tree: when
the step `i` is the tick of every awake validator at `t` and puts `u`'s attestation `a` on the
wire, some block `D` of `u`'s tree after `i` steps has `(M.chainStateOf S.C D).h = a.h`.

Why: the validator client built `a` at the height of the chain state of the source `ac_to_fg`
answered (Lemma 49), a block of the frame's tree, whose chain state is its own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `u`: the sender; `a`: the
  attestation.

Read aloud: the attestation a tick puts on the wire has the chain-state height of a block of the
sender's tree. -/
theorem tick_attestation_source (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {u : V}
    {a : Attestation V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick u t)
    -- the step `i` put `u`'s attestation `a` on the wire
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ D ∈ (x.st i u).tree, (M.chainStateOf S.C D).h = a.h := by
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  -- the tick's input state satisfies the node invariant (a wake keeps it)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput u t) := by
    rw [show x.tickInput u t = x.st i u by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E (i := i) (v := u) (by assumption)]]
    exact (lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick (by assumption))).1
  -- Lemma 49 over the record (T8, the field `tick_attestation` of `F.tk3`): the source is the
  -- deepest fast block of the outcome in the viable tree of the input state's frame, and the
  -- validator client built `a` at the height of the source's chain state (`AttestationFrom`)
  obtain ⟨-, -, D, head, hsrc, -, ⟨τ, -, -, rfl⟩, -⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
    hrun hInvT ha
  have hDT : D ∈ (x.st i u).tree := by
    rw [show x.st i u = x.tickInput u t by unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl]]
    exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1
      ((GoldilocksCorrectness.Record.Proofs.Routines.ac_to_fg_source_mem M F) _ _ D hsrc)).1
  exact ⟨D, hDT, rfl⟩

/-- The attestation a tick sends has the chain-state height of a block of the sender's tree that is
its finalized block or a descendant of it: when the step `i` is the tick of every awake validator
at `t` and puts `u`'s attestation `a` on the wire, some block `D` of `u`'s tree after `i` steps has
`(M.chainStateOf S.C D).h = a.h`, and `u`'s finalized block after `i` steps is `D` or an ancestor
of `D`. `tick_attestation_source` without the second clause.

Why: the source `ac_to_fg` answered is a block of the frame's tree (Lemma 49), whose members are the
blocks of the tree that descend from the finalized block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `u`: the sender; `a`: the
  attestation.

Read aloud: the attestation a tick puts on the wire has the chain-state height of a block of the
sender's tree that descends from its finalized block. -/
theorem tick_attestation_source_finalized (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {u : V}
    {a : Attestation V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick u t)
    -- the step `i` put `u`'s attestation `a` on the wire
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    ∃ D ∈ (x.st i u).tree, (M.chainStateOf S.C D).h = a.h ∧ (x.st i u).finalized.AncestorEq D := by
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hsent
  have hTI : x.tickInput u t = x.st i u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput u t) := by
    rw [hTI]
    exact (lem11_node_invariant M F S A x R E i u (E.not_mem_corrupted_of_tick (by assumption))).1
  obtain ⟨-, -, D, head, hsrc, -, ⟨τ, -, -, rfl⟩, -⟩ := (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
    hrun hInvT ha
  have hΦ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1
    ((GoldilocksCorrectness.Record.Proofs.Routines.ac_to_fg_source_mem M F) _ _ D hsrc)
  rw [hTI] at hΦ
  exact ⟨D, hΦ.1, rfl, hΦ.2⟩

/-- A validator active throughout a window holding a time `t₁ ≥ 1` is outside the adversary set
after the step before `t₁`: the configuration after that step is in force at `t₁`, a time of the
window, since that step is at a time less than `t₁` and the next one at a time at least `t₁`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `w`: the validator;
  `a`, `c`: the window's ends; `t₁`: the time.

Read aloud: a validator active through a window is honest just before every time of it from `1`
on. -/
theorem not_mem_corrupted_stepBefore_of_mem_activeThroughout (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {w : V} {a c t₁ : ℕ} (h1 : 1 ≤ t₁) (ha : a ≤ t₁) (hc : t₁ ≤ c)
    (hw : w ∈ A.activeThroughout x a c) : w ∉ A.corrupted (x.stepBefore t₁) := by
  -- the configuration after the step before `t₁` is in force at `t₁`, inside the window
  obtain ⟨h1t, h2t⟩ := (stepBefore_time M) x R E h1
  have hcR : (t₁ : ℝ) ≤ c := by exact_mod_cast hc
  have haR : (a : ℝ) ≤ t₁ := by exact_mod_cast ha
  exact Activity.not_mem_corrupted_of_mem_active
    (Activity.mem_activeThroughout.1 hw (x.stepBefore t₁) (by linarith) (by linarith))

/-! ## Lemma 89a -/

/-- **Lemma 89a, Lemma 68's honest corollary.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hRoots`: roots
  name blocks; `i`, `j`: the two steps; `p`, `w`: the two holders; `B`, `B'`: the two blocks.

Roots name blocks until `tR`, at least `max x[i].time x[j].time`: the proof compares an ancestor of
`B`, held after `i` steps, with an ancestor of `B'`, held after `j` steps.

Read aloud: the block finalized by the chain state of a block `p` holds at step `i` is `B'` or an
ancestor of `B'`, when `B'`, held by `w` at step `j`, has a chain-state height greater than that
finalization height, both holders are honest at their steps, and fewer than a third of the
validators have been corrupted up to the later of the two times. -/
theorem lem68_honest_past_finalized (Fx : FixedValidators M.toSlotLayout)
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

/-! ## Lemma 89b -/

/-- **Lemma 89b over the reader's time, at any earlier tick of the reader, with the slot layout uniform.** The
argument of `lem89b_at_uniformSchedule`, with the reader's earlier tick to any clock value `c₂` that is at least `t'` and
`t₀` and at least one delay before `t` (a helper, no audited text; `lem89b_at_uniformSchedule` is its instance at
`c₂ := t − Δ S`, B2 reads it at `c₂ := T₁`).

Why: as `lem89b_at_uniformSchedule`; the delivery kit reads the receiver's tick to `c₂`, and both blocks it delivers have
their slot start at most `c₂`: `D`'s at most `u`'s clock value before its tick, at most `t' ≤ c₂`; `F_u`'s more than three
delays before `t₀ ≤ c₂`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `c₂`: the clock value of the reader's earlier tick; the others as in `lem89b_at`.

Read aloud: as `lem89b_at`, when the model's slots are spaced as Goldilocks spaces them, with `v`'s earlier tick to any
clock value from the later of `t'` and `t₀` to one delay before `t` in place of its tick to `t − Δ S`. -/
theorem lem89b_at_uniformSchedule_tick (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t t' i b t₀ : ℕ) (u v : V) (a : Attestation V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v t)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ t₀) (ht₀ : t₀ + max (Δ S) Δs ≤ t)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time (x.tickStep v t)))
    (ht' : t' + Δ S ≤ t)
    (hv : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → i ≤ x.tickStep v t → v ∈ A.active i)
    (hvk : ∃ k : ℕ, x.lbl k = Event.tick v t)
    (c₂ : ℕ) (hvt : ∃ k : ℕ, x.lbl k = Event.tick v c₂) (hc₂ : c₂ + Δ S ≤ t) (ht'c₂ : t' ≤ c₂)
    (ht₀c₂ : t₀ ≤ c₂)
    (hu : u ∈ A.activeThroughout x t₀ (t₀ + Δs))
    (hSend : x.lbl i = Event.tick u t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hb : t ≤ b) :
    a.h ≤ hMax M S.C (x.tickInput v t) := by
  obtain ⟨hl, hsent⟩ := hSend
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  obtain ⟨D, hDT, hDh, -⟩ := (tick_attestation_source_finalized M F) x R E hl hsent
  obtain ⟨kV, hkV⟩ := hvk
  obtain ⟨k₂, hk₂⟩ := hvt
  have hks : x.tickStep v t = kV := (tickStep_eq_of_lbl M) x E hkV
  rw [show x.tickInput v t = x.st kV v by show x.st (x.tickStep v t) v = x.st kV v; rw [hks]]
  rw [hks] at hRoots hThird hv
  have hvh : v ∉ A.corrupted kV := E.not_mem_corrupted_of_tick hkV
  have hkVt := (E.tick_active kV v t hkV).2.1
  have hiT := (E.tick_active i u t' hl).2.2
  have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have ht₀R : (t₀ : ℝ) + Δ S ≤ t := by exact_mod_cast (show t₀ + Δ S ≤ t by omega)
  have ht'R : (t' : ℝ) + Δ S ≤ t := by exact_mod_cast ht'
  have hiV : x.time i ≤ x.time kV := by linarith
  -- `v`'s finalized block at `kV` is the finalized block of the chain state of a block `Bv` it holds there
  obtain ⟨Bv, hBv, hFv⟩ := (finalizedFromChain_of_exec M F) S A x R E kV v
  have hBvh : (M.chainStateOf S.C Bv).h ≤ hMax M S.C (x.st kV v) :=
    GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hBv
  have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Bv Bv).1
  by_contra hcon
  push Not at hcon
  -- a block `u` holds at a step no later than `kV`, higher than `v`'s greatest chain-state height, is compatible with
  -- `v`'s finalized block (Lemma 68) and is not the genesis block
  have hFw : ∀ (kU : ℕ) (X : Block V), x.time kU ≤ x.time kV → u ∉ A.corrupted kU → X ∈ (x.st kU u).tree →
      hMax M S.C (x.st kV v) < (M.chainStateOf S.C X).h → (x.st kV v).finalized.compatible X = true := by
    intro kU X h1 h2 h3 h4
    have hlt : (M.chainStateOf S.C Bv).h_F < (M.chainStateOf S.C X).h :=
      lt_of_le_of_lt h47.2.2 (lt_trans h47.2.1 (lt_of_le_of_lt hBvh h4))
    have hFX := (lem68_honest_past_finalized M F Fx) S A x R E hRoots kV kU v u Bv X
      (hThird.mono (max_le le_rfl h1)) hvh h2 hBv h3 hlt (max_le le_rfl h1)
    rw [hFv]
    exact (compatible_iff _ _).2 (Or.inl hFX)
  have hng : ∀ X : Block V, hMax M S.C (x.st kV v) < (M.chainStateOf S.C X).h → X ≠ Block.genesis := by
    intro X hX hg
    subst hg
    have := GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C)
      ((genesis_mem_T_of_exec M F) S A x R E kV v)
    unfold Height at *
    omega
  have hsl : ∀ c : ℕ, M.slot S.C c = S.C.slot (c : Int) := fun c => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hwin : ∀ j : ℕ, (t₀ : ℝ) ≤ x.time j → j ≤ kV → v ∈ A.active j := hv
  have hrt : (x.time kV : ℝ) ≤ x.time kV := le_rfl
  -- `u` is honest at its last step before `t₀`, a step at a real time at most `t₀`
  have hs₀t : x.time (x.stepBefore t₀) ≤ t₀ := (time_stepBefore_le M) x R E t₀
  have hus₀ : u ∉ A.corrupted (x.stepBefore t₀) := by
    have h := Activity.mem_activeThroughout.1 hu (x.stepBefore t₀) (by
      have : (0 : ℝ) ≤ Δs := Nat.cast_nonneg _
      linarith) ((le_time_stepBefore_succ M) x R E t₀)
    exact (Activity.mem_active.1 h).2
  have hs₀V : x.time (x.stepBefore t₀) ≤ x.time kV := by linarith
  by_cases hc : (x.st (x.stepBefore t₀) u).finalized.compatible D = true
  · -- `D` reaches `v`: its slot starts at most at `u`'s clock value before its tick, at most `t'`
    have hHs := (slot_le_clockValue_of_mem_tree M F) R E hui hDT
    rw [← hsl] at hHs
    have hcl : x.clockValue i u ≤ t' :=
      E.clockValue_le_of_set hui (Or.inl hl)
    have hDc₂ : M.slotStart S.C D.slot ≤ c₂ := by
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S D.slot
        (x.clockValue i u)).2 hHs
      omega
    have hDh' : hMax M S.C (x.st kV v) < (M.chainStateOf S.C D).h := by rw [hDh]; exact hcon
    have hDv := block_at_tick_of_held_tick M F U S A x R GST b t' i t₀ t c₂ kV k₂ u v D E hNet hSkew
      hRedeliver Sy hRoots hParent hGST ht₀ ht' hb hu hl hDT hc (hng D hDh') hkV hwin hk₂ hc₂ hDc₂
      (hFw i D hiV hui hDT hDh')
    have := GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hDv
    unfold Height at *
    omega
  · -- `u`'s finalized block before `t₀` conflicts with `D`: the finalized block `F_u` of the chain state of a block
    -- `Bu` `u` holds there, at a finalization height at least `h(D)` (Lemma 68), reaches `v`
    obtain ⟨Bu, hBu, hFu⟩ := (finalizedFromChain_of_exec M F) S A x R E (x.stepBefore t₀) u
    have hge : (M.chainStateOf S.C D).h ≤ (M.chainStateOf S.C Bu).h_F := by
      by_contra hlt
      push Not at hlt
      have hFD := (lem68_honest_past_finalized M F Fx) S A x R E hRoots (x.stepBefore t₀) i u u Bu D
        (hThird.mono (max_le hs₀V hiV)) hus₀ hui hBu hDT hlt (max_le hs₀V hiV)
      apply hc
      rw [hFu]
      exact (compatible_iff _ _).2 (Or.inl hFD)
    have hF1 : 1 ≤ (M.chainStateOf S.C Bu).h_F := by
      have := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1
      unfold Height at *
      omega
    have hcert := ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Bu).2.2 hF1
    have hFh := hcert.2.2.2
    have hInvU := (lem11_node_invariant M F S A x R E (x.stepBefore t₀) u hus₀).1
    have hFT : (x.st (x.stepBefore t₀) u).finalized ∈ (x.st (x.stepBefore t₀) u).tree :=
      F.nd.nodeInv_finalized_mem_tree hInvU
    have hFuh : (M.chainStateOf S.C (x.st (x.stepBefore t₀) u).finalized).h = (M.chainStateOf S.C Bu).h_F := by
      rw [hFu, hFh]
    have hFuh' : hMax M S.C (x.st kV v) < (M.chainStateOf S.C (x.st (x.stepBefore t₀) u).finalized).h := by
      rw [hFuh]
      unfold Height at *
      omega
    -- `F_u`'s slot starts at least four delays before `Bu`'s, at most `u`'s clock value there, less than `t₀ + ΔClockAhead`
    have hFanc : (x.st (x.stepBefore t₀) u).finalized.AncestorEq Bu := by
      rw [hFu]
      exact hcert.2.2.1
    have hne : (x.st (x.stepBefore t₀) u).finalized ≠ Bu := by
      intro h
      have h47u := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Bu Bu).1
      rw [h] at hFuh
      have e1 := h47u.2.1
      have e2 := h47u.2.2
      unfold Height at *
      omega
    have hTC := F.nd.nodeInv_treeClosed hInvU
    have hslt : (x.st (x.stepBefore t₀) u).finalized.slot < Bu.slot := by
      have key : ∀ (B Dn : Block V), Dn ∈ (x.st (x.stepBefore t₀) u).tree → B.AncestorEq Dn → B ≠ Dn →
          B.slot < Dn.slot := by
        intro B Dn hD hBD hne'
        unfold GoldilocksCorrectness.Record.Statements.Routines.TreeClosed at hTC
        induction Dn with
        | genesis =>
            exact absurd ((GoldilocksCorrectness.Proofs.Routines.ancestorEq_genesis_iff B).1 hBD) hne'
        | node p s r votes support ats v' ih =>
            rcases (GoldilocksCorrectness.Proofs.Routines.ancestorEq_node_iff B p s r votes support ats v').1
                hBD with h | h
            · exact absurd h hne'
            · obtain ⟨hpT, -, -, hps⟩ := hTC.2 _ hD (fun h' => by cases h')
              have hps' : p.slot < s := hps
              by_cases hBp : B = p
              · rw [hBp]
                exact hps'
              · exact lt_trans (ih hpT h hBp) hps'
      exact key _ _ hBu hFanc hne
    have hHs := (slot_le_clockValue_of_mem_tree M F) R E hus₀ hBu
    rw [← hsl] at hHs
    have hBs := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S Bu.slot
      (x.clockValue (x.stepBefore t₀) u)).2 hHs
    have hmono := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show (x.st (x.stepBefore t₀) u).finalized.slot + 1 ≤ Bu.slot from hslt)
    obtain ⟨-, -, -, hs4, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S
      (x.st (x.stepBefore t₀) u).finalized.slot
    have hcv := (clockValue_le_time_add_ahead M F) x R E (x.stepBefore t₀) u
    have hDc₂ : M.slotStart S.C (x.st (x.stepBefore t₀) u).finalized.slot ≤ c₂ := by
      have h1 : ((M.slotStart S.C (x.st (x.stepBefore t₀) u).finalized.slot : ℕ) : ℝ) + 4 * Δ S ≤
          (x.clockValue (x.stepBefore t₀) u : ℝ) := by
        have h1n : M.slotStart S.C (x.st (x.stepBefore t₀) u).finalized.slot + 4 * Δ S ≤
            x.clockValue (x.stepBefore t₀) u := by omega
        exact_mod_cast h1n
      have h2 : (x.clockValue (x.stepBefore t₀) u : ℝ) < (t₀ : ℝ) + Δ S := by
        have : max 0 (x.time (x.stepBefore t₀) + ΔClockAhead) < (t₀ : ℝ) + Δ S :=
          max_lt (by positivity) (by linarith)
        linarith
      have hc₀ : (t₀ : ℝ) ≤ c₂ := by exact_mod_cast ht₀c₂
      have h3 : ((M.slotStart S.C (x.st (x.stepBefore t₀) u).finalized.slot : ℕ) : ℝ) ≤ c₂ := by linarith
      exact_mod_cast h3
    have hFv' := block_at_tick_of_held_step M F U S A x R GST b t₀ (x.stepBefore t₀) t₀ t c₂ kV k₂ u v
      (x.st (x.stepBefore t₀) u).finalized E hNet hSkew hRedeliver Sy hRoots hParent hGST ht₀ (by omega) hb hu
      hs₀t hus₀ hFT ((compatible_iff _ _).2 (Or.inl (GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl _)))
      (hng _ hFuh') hkV hwin hk₂ hc₂ hDc₂ (hFw _ _ hs₀V hus₀ hFT hFuh')
    have := GoldilocksCorrectness.Record.Statements.Routines.le_hMax M (C := S.C) hFv'
    unfold Height at *
    omega

/-- **Lemma 89b over the reader's time, with the slot layout uniform (a copy of `lem89b_at`).** `lem89b_at` with the
added hypothesis `U : UniformSchedule M.toSlotLayout`, the model's slots spaced as Goldilocks spaces its slots: the
delivery kit `block_at_tick_of_held_tick`, `block_at_tick_of_held_step` reads the protocol's slot of the receiver's
clock value through it (`mem_tree_of_admitted_delivery`). Made on a copy under the away rule; `lem89b_at` now takes `U` too and is proved by this copy.

Why: suppose `v`'s greatest chain-state height at its tick `kV` to `t` is less than `a.h`. `a`'s source `D` is in
`u`'s tree at its tick `i` to `t'`, at the chain-state height `a.h`. When `u`'s finalized block at its last step
before `t₀` is compatible with `D`, `D` reaches `v`'s tick input to `t` (`block_at_tick_of_held_tick`: `D`'s slot
starts at most at `u`'s clock value before its tick, at most `t' ≤ t − Δ S`; `v`'s finalized block there is an
ancestor of `D`, Lemma 68); otherwise that finalized block `F_u` is the finalized block of the chain state of a block
`Bu` `u` holds there, at a height at least `a.h` (Lemma 68), and `F_u` reaches `v` (`block_at_tick_of_held_step`):
`F_u` is an ancestor of `Bu` other than `Bu` (Lemma 47), so its slot is less than `Bu`'s, whose start is at most
`u`'s clock value there, less than `t₀ + ΔClockAhead`; so `F_u`'s slot starts at most `t − Δ S`. Either block then
is in `v`'s tree at `kV`, against the height.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others as in `lem89b_at`.

Read aloud: as `lem89b_at`, when the model's slots are spaced as Goldilocks spaces them. -/
theorem lem89b_at_uniformSchedule (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t t' i b t₀ : ℕ) (u v : V) (a : Attestation V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v t)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ t₀) (ht₀ : t₀ + max (Δ S) Δs ≤ t)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time (x.tickStep v t)))
    (ht' : t' + Δ S ≤ t)
    (hv : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → i ≤ x.tickStep v t → v ∈ A.active i)
    (hvk : ∃ k : ℕ, x.lbl k = Event.tick v t)
    (hvt : ∃ k : ℕ, x.lbl k = Event.tick v (t - Δ S))
    (hu : u ∈ A.activeThroughout x t₀ (t₀ + Δs))
    (hSend : x.lbl i = Event.tick u t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hb : t ≤ b) :
    a.h ≤ hMax M S.C (x.tickInput v t) :=
  lem89b_at_uniformSchedule_tick M F U Fx S A x R GST t t' i b t₀ u v a E hNet hSkew hRedeliver Sy hΔs hRoots hParent
    hGST ht₀ hThird ht' hv hvk (t - Δ S) hvt
    (by have := one_le_Δ S; omega) (by omega) (by have := le_max_left (Δ S) Δs; omega) hu hSend hb

/-- **Lemma 89b over the reader's time.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`. It is the proof of Lemma 89b with the facts it
reads of the phase as hypotheses: `GST + max (Δ S) Δs ≤ t`, the adversary bound at `t`,
`t' + Δ S ≤ t`, `v` awake and honest at every time from `t − max (Δ S) Δs` to `t`, and `u` awake and
honest from `t − max (Δ S) Δs` through the later of that time and `t'`. The
block that reaches `v` is the attestation's source `D` when `u` serves it at its tick (the tick in
the window) or at the window's start; otherwise `u`'s finalized block at the window's start, which
conflicts with `D` and so is at least as high (Lemma 89a).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the clock value of `v`'s tick whose input is read; `t'`: the time of `u`'s tick; `i`: its step; `b`: the
  bound on the deadlines;
- `u`: the attester; `v`: the validator whose greatest chain-state height is read; `a`: the
  attestation.

Restated with the delivery premises up to `b`, the latest deadline being `t`, and roots named
until the real time of `v`'s tick to `t`, where `v`'s finalized block is compared (the
attestation's source block, which `u` holds before `t' ≤ t − Δ S`, reaching `v` by `t`).

Read aloud: from a time `t₀` after `GST` and at least one delay or one sync delay before
`t`, with `v` active from `t₀` up to its tick to `t` and `u` active from `t₀` for one sync delay, fewer
than a third of the validators corrupted up to the real time of `v`'s tick to `t`, and `u`'s attestation
sent at its tick to `t' ≤ t − Δ S`, the attestation's height is at most `v`'s greatest chain-state height at
its tick to `t`. -/
theorem lem89b_at (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t t' i b t₀ : ℕ) (u v : V) (a : Attestation V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v t)))
    (hParent : ParentHeldAtDelivery M x)
    -- the window starts at `t₀`, from `GST` on, at least the recovery delay `max (Δ S) Δs` before `t`
    (hGST : GST ≤ t₀) (ht₀ : t₀ + max (Δ S) Δs ≤ t)
    -- fewer than a third of the validators have been in the adversary set up to the real time of `v`'s
    -- tick to `t`
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time (x.tickStep v t)))
    -- `t` is at least one delay after `t'`
    (ht' : t' + Δ S ≤ t)
    -- `v` is active after every step whose real time is at least `t₀`, up to its tick to `t`, which exists
    (hv : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → i ≤ x.tickStep v t → v ∈ A.active i)
    (hvk : ∃ k : ℕ, x.lbl k = Event.tick v t)
    -- `v` ticked to the clock value one delay before `t`
    (hvt : ∃ k : ℕ, x.lbl k = Event.tick v (t - Δ S))
    -- `u` is awake and honest at every time from `t₀` for one sync delay
    (hu : u ∈ A.activeThroughout x t₀ (t₀ + Δs))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = Event.tick u t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the latest deadline the proof reads is at most the bound
    (hb : t ≤ b) :
    a.h ≤ hMax M S.C (x.tickInput v t) := by
  exact lem89b_at_uniformSchedule M F U Fx S A x R GST t t' i b t₀ u v a E hNet hSkew hRedeliver Sy hΔs hRoots
    hParent hGST ht₀ hThird ht' hv hvk hvt hu hSend hb


/-- **Lemma 89b, the honest greatest chain-state height keeps up with the honest attestations.** The
proof; the audited statement is in `Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `t`: the clock value of `v`'s tick whose input is read; `t'`: the time of `u`'s tick; `i`: its step;
- `u`: the attester; `v`: the validator whose greatest chain-state height is read; `a`: the
  attestation.

Roots name blocks until the real time of `v`'s tick to `t`: `lem89b_at`, which the proof calls with
`b := t`, compares `v`'s finalized block at that tick.

Read aloud: in the phase, no honest validator's greatest chain-state height lags more than one delay
behind the heights honest attestations name. -/
theorem lem89b_h_max_ge_attested (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd t t' i : ℕ) (u v : V)
    (a : Attestation V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v t)))
    (hParent : ParentHeldAtDelivery M x)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- `t` is at least `max (Δ S) Δs` into the phase, and at least one delay after `t'`
    (ht : tGAT + max (Δ S) Δs ≤ t) (ht' : t' + Δ S ≤ t) (htEnd : t ≤ tAwakeEnd)
    -- `v`'s tick to `t` is in the phase
    (htEndv : x.time (x.tickStep v t) ≤ tAwakeEnd)
    -- `v` is awake and honest from `max (Δ S) Δs` before `t` to its tick to `t`
    (hv : v ∈ A.activeThroughoutToTick x ((t - max (Δ S) Δs : ℕ) : ℤ) t)
    -- `v` ticked to the clock value one delay before `t`
    (hvt : ∃ k : ℕ, x.lbl k = Event.tick v (t - Δ S))
    -- `u` is honest at the later of its tick and one sync delay after `max (Δ S) Δs` before `t`
    (hu : u ∉ A.corruptedAtTime x (max t' ((t - max (Δ S) Δs) + Δs)))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = Event.tick u t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    a.h ≤ hMax M S.C (x.tickInput v t) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hmx := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  -- `v`'s tick `k'` to `t`, honest there
  obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hks : x.tickStep v t = k' := (tickStep_eq_of_lbl M) x E hk'
  have hvk' : v ∉ A.corrupted k' := E.not_mem_corrupted_of_tick hk'
  have htGR : (tGAT : ℝ) ≤ ((t - max (Δ S) Δs : ℕ) : ℝ) := by
    exact_mod_cast (show tGAT ≤ t - max (Δ S) Δs by omega)
  have hEndR : ((t - max (Δ S) Δs : ℕ) : ℝ) + Δs ≤ (tAwakeEnd : ℝ) := by
    exact_mod_cast (show t - max (Δ S) Δs + Δs ≤ tAwakeEnd by omega)
  refine (lem89b_at M F U Fx) S A x R GST t t' i t (t - max (Δ S) Δs) u v a (E.upTo t) hNet hSkew hRedeliver
    (Sy.upTo t) hΔs hRoots hParent (by omega) (by omega) ?_ ht' ?_ ⟨k', hk'⟩ hvt ?_ hSend le_rfl
  · -- the adversary bound up to the phase's end covers `v`'s tick
    intro X hX
    exact hThird X fun w hw => by
      obtain ⟨j, hj, hc⟩ := hX w hw
      exact ⟨j, le_trans hj htEndv, hc⟩
  · -- `v`, honest at its tick, is awake at every earlier step in the phase
    intro j h1 h2
    rw [hks] at h2
    have hcj : v ∉ A.corrupted j := E.not_mem_corrupted_of_le h2 hvk'
    have hT : x.time j ≤ x.time k' := R.time_mono h2
    rw [hks] at htEndv
    exact Activity.mem_active.2 ⟨hAwake j v (le_trans hT htEndv)
      (le_trans htGR (le_trans h1 (R.time_mono (Nat.le_succ j)))) hcj, hcj⟩
  · -- `u`, honest up to one sync delay after the window's start, is awake from it
    refine Activity.mem_activeThroughout.2 fun j h1 h2 => ?_
    have hsub : ((t - max (Δ S) Δs : ℕ) : ℝ) = (t : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ) := Nat.cast_sub (by omega)
    have hcj : u ∉ A.corrupted j :=
      Activity.not_mem_corruptedAtTime.1 hu j (le_trans h1 (by rw [hsub]; exact le_max_right _ _))
    exact Activity.mem_active.2 ⟨hAwake j u (le_trans h1 hEndR) (le_trans htGR h2) hcj, hcj⟩

/-! ## Lemma 89h -/

/-- **Lemma 89h, the threshold.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `r₀`: the round; `s₀`: its first slot; `B₀`: the proposal; `p₀`: its proposer.

Roots name blocks until the real time of `p₀`'s tick to the start of slot `s₀`: `lem89b_at`, which the
proof calls at `p₀`'s tick there, compares `p₀`'s finalized block at that tick.

Read aloud: every honest attestation sent before the action time of the healed round has height at
most `h(B₀) + 1`. -/
theorem lem89h_threshold (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r₀ s₀ : ℕ) (B₀ : Block V) (p₀ : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p₀ (M.slotStart S.C s₀))))
    (hParent : ParentHeldAtDelivery M x)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- `s₀` is the first slot of round `r₀`, and not slot `0`
    (hs₀ : s₀ = r₀ * S.C.R) (hs₁ : 1 ≤ s₀)
    -- slot `s₀` starts at least `max (Δ S) Δs` into the phase, and its round acts inside the phase
    (hFirst : tGAT + max (Δ S) Δs ≤ M.slotStart S.C s₀) (hEnd : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd)
    -- `p₀` is honest at the start of slot `s₀`
    (hp₀ : p₀ ∉ A.corruptedAtTime x (M.slotStart S.C s₀))
    -- `p₀` ticked to the clock value one delay before the start of slot `s₀`
    (hp₀t : ∃ k : ℕ, x.lbl k = Event.tick p₀ (M.slotStart S.C s₀ - Δ S))
    -- `p₀`'s tick at the start of slot `s₀` put `B₀` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p₀ (M.slotStart S.C s₀) ∧
      (⟨p₀, NamedObject.block B₀⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B₀`'s parent is in the viable tree of `p₀`'s frame before the start of slot `s₀`
    (hParentIn : B₀.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p₀ (M.slotStart S.C s₀)))
      (M.fg_to_ac (x.tickInput p₀ (M.slotStart S.C s₀))).tree) :
    OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1))
      ((M.chainStateOf S.C B₀).h + 1) := by
  intro i t v a hl ht hvH hSent
  have hΔ := one_le_Δ S
  have hRR := S.C.R_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hmx := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- the attesting tick is at the action time of a round `r` (Lemma 49)
  obtain ⟨-, n', sent, hrun, ha⟩ := (tick_send_of_honestSendAt M F R E) hl hSent
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) := by
    rw [show x.tickInput v t = x.st i v by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]]
    exact (lem11_node_invariant M F S A x R E i v (E.not_mem_corrupted_of_tick hl)).1
  obtain ⟨hT, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a hrun
      hInvT ha
  have hsl : S.C.slot ((t : ℕ) : Int) = M.slot S.C t := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
  rw [hsl] at hT
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = S.C.round (M.slot S.C t) := ⟨_, rfl⟩
  obtain ⟨hslot, hround, hcut, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_times M.toSlotLayout F.sched U) S r
      (r * S.C.R) rfl
  rw [hslot, hround] at hcut
  rw [← hr] at hT
  have htr0 : t = M.supportCutoff S.C (r * S.C.R + 1) := by
    have h : ((t : ℕ) : Int) = ((M.supportCutoff S.C (r * S.C.R + 1) : ℕ) : Int) := hT.trans hcut.symm
    exact_mod_cast h
  have hcutE : ∀ s : ℕ, M.supportCutoff S.C (s + 1) = 4 * Δ S * s + 6 * Δ S := fun s => by
    obtain ⟨-, hc, -, hs4, -⟩ :=
      (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
    rw [hc, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1),
      Nat.mul_add, Nat.mul_one]
    omega
  have hstart : M.slotStart S.C s₀ = 4 * Δ S * s₀ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s₀
  have htr : t = 4 * Δ S * (r * S.C.R) + 6 * Δ S := by rw [htr0, hcutE]
  have htN : t < M.supportCutoff S.C (s₀ + 1) := by exact_mod_cast ht
  rw [hcutE] at htN
  have hrR : r * S.C.R < s₀ := by
    rw [htr] at htN
    have h4 : 4 * Δ S * (r * S.C.R) < 4 * Δ S * s₀ := by omega
    exact Nat.lt_of_mul_lt_mul_left h4
  have hrr : r < r₀ := by
    rw [hs₀] at hrR
    exact Nat.lt_of_mul_lt_mul_right hrR
  have hle : r * S.C.R + 2 ≤ s₀ := by
    have : (r + 1) * S.C.R ≤ r₀ * S.C.R := Nat.mul_le_mul_right _ hrr
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have ht' : t + Δ S ≤ M.slotStart S.C s₀ := by
    have h5 : 4 * Δ S * (r * S.C.R + 2) ≤ 4 * Δ S * s₀ := Nat.mul_le_mul_left _ hle
    rw [Nat.mul_add] at h5
    rw [htr, hstart]
    omega
  -- `p₀`'s tick `i₀` to the start of slot `s₀`, honest there, inside the phase
  obtain ⟨i₀, hl₀, hsent₀⟩ := hPropose
  have hks : x.tickStep p₀ (M.slotStart S.C s₀) = i₀ := (tickStep_eq_of_lbl M) x E hl₀
  have hp₀i : p₀ ∉ A.corrupted i₀ := E.not_mem_corrupted_of_tick hl₀
  have hi₀t := (E.tick_active i₀ p₀ _ hl₀).2.2
  obtain ⟨-, hc₀, -, hs₀4, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s₀
  obtain ⟨-, hc₁, -, -, -⟩ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s₀ + 1)
  have hi₀End : x.time i₀ ≤ (tAwakeEnd : ℝ) := by
    have h1 : ((M.slotStart S.C s₀ : ℕ) : ℝ) + Δ S ≤ (tAwakeEnd : ℝ) := by
      exact_mod_cast (show M.slotStart S.C s₀ + Δ S ≤ tAwakeEnd by omega)
    linarith
  have htGR : (tGAT : ℝ) ≤ ((M.slotStart S.C s₀ - max (Δ S) Δs : ℕ) : ℝ) := by
    exact_mod_cast (show tGAT ≤ M.slotStart S.C s₀ - max (Δ S) Δs by omega)
  have hEndR : ((M.slotStart S.C s₀ - max (Δ S) Δs : ℕ) : ℝ) + Δs ≤ (tAwakeEnd : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s₀ - max (Δ S) Δs + Δs ≤ tAwakeEnd by omega)
  have hcutR : ((M.slotStart S.C s₀ - max (Δ S) Δs : ℕ) : ℝ) + Δs ≤
      ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show M.slotStart S.C s₀ - max (Δ S) Δs + Δs ≤ M.supportCutoff S.C (s₀ + 1) by omega)
  -- Lemma 89b at `p₀`'s tick to the start of slot `s₀`
  have h89b := (lem89b_at M F U Fx) S A x R GST (M.slotStart S.C s₀) t i (M.slotStart S.C s₀)
    (M.slotStart S.C s₀ - max (Δ S) Δs) v p₀ a (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _) hΔs hRoots
    hParent (by omega) (by omega)
    (fun X hX => hThird X fun w hw => by
      obtain ⟨j, hj, hc⟩ := hX w hw
      exact ⟨j, le_trans hj (by rw [hks]; exact hi₀End), hc⟩)
    ht'
    (fun j h1 h2 => by
      rw [hks] at h2
      have hcj : p₀ ∉ A.corrupted j := E.not_mem_corrupted_of_le h2 hp₀i
      exact Activity.mem_active.2 ⟨hAwake j p₀ (le_trans (htime h2) hi₀End)
        (le_trans htGR (le_trans h1 (htime (Nat.le_succ j)))) hcj, hcj⟩)
    ⟨i₀, hl₀⟩ hp₀t
    (Activity.mem_activeThroughout.2 fun j h1 h2 => by
      have hcj : v ∉ A.corrupted j := Activity.not_mem_corruptedAtTime.1 hvH j (le_trans h1 hcutR)
      exact Activity.mem_active.2 ⟨hAwake j v (le_trans h1 hEndR) (le_trans htGR h2) hcj, hcj⟩)
    ⟨hl, hSent⟩ le_rfl
  -- `head_height_floor` at `p₀` is at most `B₀`'s height, and `h_max` at most one more than it
  have hs : s₀ - 1 + 1 = s₀ := by omega
  have hviable := (proposal_viable M F U) S A x R E (s₀ - 1) B₀ p₀
    (by rw [hs]; exact ⟨i₀, hl₀, hsent₀⟩) (by rw [hs]; exact hParentIn)
  rw [hs] at hviable
  have hInv₀ : M.nodeInv S.C S.P S.X (x.tickInput p₀ (M.slotStart S.C s₀)) := by
    rw [show x.tickInput p₀ (M.slotStart S.C s₀) = x.st i₀ p₀ by
      unfold Trace.tickInput
      rw [hks]]
    exact (lem11_node_invariant M F S A x R E i₀ p₀ hp₀i).1
  have hmf := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X _ hInv₀
  exact le_trans h89b (le_trans hmf (Nat.add_le_add_right hviable 1))

/-! ## The height bound from the old attestations -/

/-- **The step form of the old attestations from their clock form.** An attestation put on the wire by
a tick at a step before `i` has a clock value at most `ΔClockAhead` after the time of step `i`
(`tick_active`), so the clock form at any `t₀` greater than that bounds it.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Act`, `x`: the setup, the activity, the execution; `i`: the step; `A`: the bound on the heights;
  `tH`: the honesty time; `t₀`: a time more than `ΔClockAhead` after the time of step `i`.

Read aloud: when no honest attestation of a tick to a clock value less than `t₀` is above `A`, and `t₀` is
more than `ΔClockAhead` after step `i`, no honest attestation put on the wire by a tick at a step before `i`
is above `A`. -/
theorem oldAttestations_before_step_of_clock (S : Setup V) (Act : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy Act x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i A tH : ℕ} {t₀ : ℝ} (ht₀ : x.time i + ΔClockAhead < t₀)
    (hOld : OldAttestationsAtMostHonestAt M S Act x t₀ tH A) :
    ∀ (k t : ℕ) (u : V) (a : Attestation V), k < i → x.lbl k = Event.tick u t →
      u ∉ Act.corruptedAtTime x tH →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a.h ≤ A := by
  intro k t u a hk hl hu hs
  have h1 := (E.tick_active k u t hl).2.1
  have h2 := (time_mono M) x R (show k ≤ i by omega)
  exact hOld k t u a hl (by linarith) hu hs

/-- **The height bound from the old attestations, in the step form.** The argument of
`attested_height_bound`: the honest attestation the proof reads was sent by a tick at a step before
`i`, and `hOld` bounds it.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Act`, `x`: the setup, the activity, the execution;
- `i`: the step; `A`: the bound on the heights of the honest attestations; `v`: the holder;
  `D`: the block; `tH`: the honesty time.

Read aloud: if no honest attestation put on the wire by a tick at a step before `i` is at a height
greater than `A`, every block `v` holds after step `i` has height at most `A + 1`. -/
theorem attested_height_bound_before (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (Act : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy Act x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i A : ℕ) (v : V)
    (D : Block V) (tH : ℕ)
    (htH : x.time i ≤ tH)
    (hAdv : Act.AdversaryFewerThanThirdUntil x (validator_count V) tH)
    (hOld : ∀ (k t : ℕ) (u : V) (a : Attestation V), k < i → x.lbl k = Event.tick u t →
      u ∉ Act.corruptedAtTime x tH →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a.h ≤ A)
    (hD : D ∈ (x.st i v).tree) :
    (M.chainStateOf S.C D).h ≤ A + 1 := by
  by_contra hcon
  have hlt : A + 1 < (M.chainStateOf S.C D).h := Nat.lt_of_not_le hcon
  -- Lemma 67: an ancestor `Y` of `D` at height `A + 2` carries a certificate at height `A + 1`
  obtain ⟨Y, hYD, -, -, -, -, X, hXY, Q, hQ, hQm⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C D (A + 1) (Nat.succ_pos A) hlt
  have hY := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S Act x R E i v D Y hD hYD
  have hX := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S Act x R E i v Y X hY hXY
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hQ
  -- the certificate's quorum has a member `u` honest through the time of step `i`
  have hcard : Q.card ≤ validator_count V := Finset.card_le_univ Q
  have hQ' : 2 * quorum V - validator_count V ≤ Q.card := by omega
  obtain ⟨u, huQ, hHuH⟩ := (exists_honestThroughTime_of_card M F) Act x hAdv hQ'
  have hHu : x.HonestThrough Act i u := (honestThrough_of_time_le M F) x R hHuH htH
  obtain ⟨b, hbu, hbh, -, hon⟩ := hQm u huQ
  -- `u`'s attestation at height `A + 1` is in its record, so sent by its own tick before step `i`
  have hrec := (lem74_honest_attestations_recorded M F) S Act x R E i v X b hX hon
    (by rw [hbu]; exact hHu)
  rw [hbu] at hrec
  obtain ⟨j, t', a', hj, hl, hact_hAw, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S Act x R E u i b.content hrec
  -- the old attestations are at height at most `A`
  have ha' := hOld j t' u a' hj hl
    (Activity.not_mem_corruptedAtTime.2 fun k hk => hHuH k hk) hsent
  have hab : a'.h = b.h := congrArg AttestationContent.h hcont
  rw [hab, hbh] at ha'
  exact Nat.not_succ_le_self A ha'

/-- **The height bound from the old attestations.** The proof; the audited statement is in
`Statements/Executions/PhaseFrameStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability;
- `i`: the step; `A`: the bound on the heights of the honest attestations; `v`: the holder;
  `D`: the block.

Read aloud: if no honest attestation put on the wire by a tick at a step before `i` is at a height
greater than `A`, every block `v` holds after step `i` has height at most `A + 1`. -/
theorem attested_height_bound (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (Act : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy Act x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i A : ℕ) (v : V)
    (D : Block V) (tH : ℕ)
    (htH : x.time i ≤ tH)
    (hAdv : Act.AdversaryFewerThanThirdUntil x (validator_count V) tH)
    (hOld : ∀ (k t : ℕ) (u : V) (a : Attestation V), k < i → x.lbl k = Event.tick u t →
      u ∉ Act.corruptedAtTime x tH →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a.h ≤ A)
    (hD : D ∈ (x.st i v).tree) :
    (M.chainStateOf S.C D).h ≤ A + 1 := by
  exact (attested_height_bound_before M F Fx) S Act x R E i A v D tH htH hAdv hOld hD

end GoldilocksCorrectness.Record.Proofs.Executions

