module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.Lemma89r
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89StabilityB6, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89StabilityB6.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the kit of B6 of Lemma 89 that does
not read the fork-choice change, namely the justified block of a node state, a viable block of a
validator compared with another validator's state one delay before, an honest Goldfish vote an
ancestor of a viable block of its voter, an eligible confirmation with an honest supporter, and two
held blocks with one root one block. The page's routine-level theorems are the facts' fields or have
their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_cast supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ConfirmationUpdated)

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
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The justified block -/

/-- The justified block of a node state sits at its justification height, when that height is at
least `1`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: the justified block of a node state is at its justification height, when that height is
at least `1`. -/
theorem J_height (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) (h1 : 1 ≤ (x.stateBefore t v).justifiedHeight) :
    (M.chainStateOf S.C (x.stateBefore t v).justified).h =
      (x.stateBefore t v).justifiedHeight := by
  obtain ⟨⟨W, -, hJW, hjW⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t v
  rw [hJW, hjW]
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C W).2.2 (by rw [← hjW]; exact h1)

/-- The justified block of a node state with the cache `h_j = 0` is the genesis block.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: the justified block of a node state with justification height `0` is the genesis block.
-/
theorem J_genesis (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) (h0 : (x.stateBefore t v).justifiedHeight = 0) :
    (x.stateBefore t v).justified = Block.genesis := by
  obtain ⟨⟨W, -, hJW, hjW⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t v
  rw [hJW]
  exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C W).2.1 (by rw [← hjW]; exact h0)

/-- The justified block of a node state carries a justification certificate at the cache `h_j`
on a block the validator holds, when `h_j ≥ 1`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: the justified block of a node state has a justification certificate at its justification
height on a held block, when that height is at least `1`. -/
theorem J_cert (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) (h1 : 1 ≤ (x.stateBefore t v).justifiedHeight) :
    ∃ W ∈ (x.stateBefore t v).tree,
      JustificationCertOn M W (x.stateBefore t v).justifiedHeight
        (x.stateBefore t v).justified := by
  obtain ⟨⟨W, hW, hJW, hjW⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t v
  refine ⟨W, hW, ?_⟩
  rw [hJW, hjW]
  exact (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C W).1
    (by rw [← hjW]; exact h1)).1

/-- The justified block of a node state is in its tree.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: the justified block of a node state is in its tree. -/
theorem J_mem_T (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v : V) : (x.stateBefore t v).justified ∈ (x.stateBefore t v).tree :=
  ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E (x.stepBefore t) v).2.2.1

/-- **Two honest justified blocks at one height are one block.** Under unforgeability, roots
naming blocks, permanent corruption and fewer than a third of the validators in the adversary set
up to `tEnd`: when `p` is honest at `t ≤ tEnd`, `q` at `t' ≤ tEnd`, and their caches `h_j` agree,
their justified blocks are one block (Lemma 76; the genesis block at `h_j = 0`).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `q`: the two validators.

Roots name blocks until `tR`, at least `max t t'`: the proof compares `p`'s justified block
before `t` with `q`'s before `t'` (`eq_of_cert_same_height`).

Read aloud: two honest validators with one justification height have one justified block. -/
theorem J_eq_of_h_j_eq (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (tEnd t t' : ℕ) (p q : V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hp : p ∉ A.corruptedAtTime x t) (hq : q ∉ A.corruptedAtTime x t')
    (heq : (x.stateBefore t p).justifiedHeight = (x.stateBefore t' q).justifiedHeight)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (x.stateBefore t p).justified = (x.stateBefore t' q).justified := by
  by_cases h0 : (x.stateBefore t p).justifiedHeight = 0
  · rw [(J_genesis M F) S A x R E t p h0, (J_genesis M F) S A x R E t' q (heq ▸ h0)]
  have h1 : 1 ≤ (x.stateBefore t p).justifiedHeight := Nat.one_le_iff_ne_zero.mpr h0
  obtain ⟨W, hW, hc⟩ := (J_cert M F) S A x R E t p h1
  obtain ⟨W', hW', hc'⟩ := (J_cert M F) S A x R E t' q (heq ▸ h1)
  rw [← heq] at hc'
  exact (eq_of_cert_same_height M F Fx) S A x R E hRoots tEnd t t' p q W W' _ _ _ hThird ht ht'
    hp hq hW hW' hc hc' ((J_mem_T M F) S A x R E t p) ((J_mem_T M F) S A x R E t' q) htR

/-- **An honest finalized block at a height `f ≥ 1` is the justified block of every honest state
with the cache `h_j = f`.** As `J_eq_of_h_j_eq`, with `p`'s finalized block, finalized by the
chain state of a block `D` that `p` holds, at the finalization height `f` (Lemma 66, Lemma 76).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `q`: the two validators; `D`: the block whose chain state finalized `p`'s block.

Roots name blocks until `tR`, at least `max t t'`: the proof compares `p`'s finalized block
before `t` with `q`'s justified block before `t'` (`eq_of_cert_same_height`).

Read aloud: an honest finalized block at a height `f ≥ 1` is the justified block of every honest
node state with justification height `f`. -/
theorem F_eq_J_of_height (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (tEnd t t' : ℕ) (p q : V) (D : Block V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hp : p ∉ A.corruptedAtTime x t) (hq : q ∉ A.corruptedAtTime x t')
    (hD : D ∈ (x.stateBefore t p).tree)
      (hF : (x.stateBefore t p).finalized = (M.chainStateOf S.C D).F)
    (h1 : 1 ≤ (M.chainStateOf S.C D).h_F)
    (heq : (x.stateBefore t' q).justifiedHeight = (M.chainStateOf S.C D).h_F)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (x.stateBefore t p).finalized = (x.stateBefore t' q).justified := by
  obtain ⟨hcertF, -, hFD, -⟩ :=
    ((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2 h1
  obtain ⟨W', hW', hc'⟩ := (J_cert M F) S A x R E t' q (heq ▸ h1)
  rw [heq] at hc'
  have hFT : (M.chainStateOf S.C D).F ∈ (x.stateBefore t p).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E _ p D _ hD hFD
  rw [hF]
  exact (eq_of_cert_same_height M F Fx) S A x R E hRoots tEnd t t' p q D W' _ _ _ hThird ht ht'
    hp hq hD hW' hcertF hc' hFT ((J_mem_T M F) S A x R E t' q) htR

/-! ## A viable block of another validator -/

/-- A viable head of a validator's frame is a block it holds, the finalized block and the
fork-choice root are ancestors of it or it, and its chain-state height is at least the
`head_height_floor`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `u`: the validator;
  `W`: the block.

Read aloud: a viable head of a validator is held, has the finalized block and the fork-choice root
as ancestors or itself, and is at a chain-state height at least `head_height_floor`. -/
theorem viable_props (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (u : V) (W : Block V) (hW : W ∈ (M.fg_to_ac (x.stateBefore t u)).viable_heads) :
    W ∈ (x.stateBefore t u).tree ∧ (x.stateBefore t u).finalized.AncestorEq W ∧
      (M.get_fc_root (x.stateBefore t u)).AncestorEq W ∧
      M.head_height_floor (x.stateBefore t u) ≤ (M.chainStateOf S.C W).h := by
  obtain ⟨hT, hF, hr, hfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
    (show M.nodeInvCore S.C S.P S.X (x.stateBefore t u) from
          (lem11_node_invariantCore_of_run M F S x R (x.stepBefore t) u).1) W).1 hW
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)] at hr
  exact ⟨hT, hF, hr, hfl⟩

/-- **`floor_le_of_delivery` read at the receiver's tick**. The holder `p`, outside the adversary set up to
the time `t`, active from `a` through the sync delay after it; the receiver `w` ticks to `c`, at least `t + Δ S`, at
the step `kR`, is active at every step from the real time `a` up to that tick, and ticked earlier to `c₂`, at least the
start of the slot of every block `p` holds before `t` and one delay before `c`. Then `p`'s `head_height_floor` before
`t` is at most `w`'s at its tick.

Why: as `floor_le_of_delivery`, with the blocks `p` holds before `t` (its contest block and its justification
witness) delivered by `w`'s tick (`block_at_tick_of_held_step`) in place of by a real time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `t`: the time `p`'s state is read before; `a`: the start of the windows; `c`, `kR`: the clock value
  and the step of `w`'s tick; `c₂`, `k₂`: those of its earlier tick; `p`, `w`: the holder and the receiver.

Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: the `head_height_floor` of an honest validator before a time is at most that of another, read at its
tick one delay later. -/
theorem floor_le_of_delivery_tick (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t a c c₂ kR k₂ : ℕ) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a third of the validators have been in the adversary set up to the real time of `kR`
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kR))
    -- from `a` on, one delay or one sync delay before `t + Δ`, the network is synchronous
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S)
    -- the holder `p`, active from `a` through the sync delay after it, outside the adversary set up to `t`
    (hv₀ : p ∈ A.activeThroughout x a (a + Δs)) (hp : p ∉ A.corruptedAtTime x t)
    -- the receiver `w`'s tick to `c`, at least one delay after `t`, and its window from `a`
    (hkR : x.lbl kR = Event.tick w c) (hcu : t + Δ S ≤ c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- an earlier tick of `w` to `c₂`, one delay before `c`, at least the start of every slot of `p`'s blocks
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t p).tree, M.slotStart S.C Y.slot ≤ c₂)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR) :
    M.head_height_floor (x.stateBefore t p) ≤ M.head_height_floor (x.st kR w) := by
  -- `dev`'s proof of `floor_le_of_delivery_unordered`, with `w` read at its tick `kR` (rule R3) and `p`'s blocks
  -- delivered by that tick (`block_at_tick_of_held_step`) in place of by the real time `t + Δ S` (F-P1-25-1)
  classical
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨kp, hkp⟩ : ∃ kp : ℕ, kp = x.stepBefore t := ⟨_, rfl⟩
  have hsb : x.stateBefore t p = x.st kp p := by rw [hkp]; rfl
  rw [hsb] at hslot ⊢
  have hkpt : x.time kp ≤ (t : ℝ) := by rw [hkp]; exact (time_stepBefore_le M) x R E t
  have hpk : p ∉ A.corrupted kp := (not_mem_corrupted_of_le_time M) x R E hp hkpt
  have hwk : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hcuR : (t : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hcu
  have hkpR : x.time kp ≤ x.time kR := by linarith
  have hkpR' : x.time kp ≤ tR := hkpR.trans htR
  have hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (max (x.time kR) (x.time kp)) :=
    hAdv.mono (max_le le_rfl hkpR)
  have htRt : ((t : ℕ) : ℝ) ≤ tR := by linarith
  have hRootsT : RootsNameBlocksUntil M A x (t : ℕ) :=
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htRt hRoots
  -- the invariants of the two states
  have hInvP := (lem11_node_invariant M F S A x R E kp p hpk).1
  have hInvW := (lem11_node_invariant M F S A x R E kR w hwk).1
  have hCacheW : GoldilocksCorrectness.Record.Statements.Routines.HeightCacheBounds M S.C (x.st kR w) :=
    fun _ hB => GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hB
  -- every block `p` holds at `kp` (compatible with its finalized block there) that is compatible with `w`'s
  -- finalized block at `kR` reaches `w` by its tick `kR`
  have hreach : ∀ Y ∈ (x.st kp p).tree,
      (x.st kp p).finalized.compatible Y = true →
      (x.st kR w).finalized.compatible Y = true →
      Y ∈ (x.st kR w).tree := by
    intro Y hY hsel hc
    by_cases hg : Y = Block.genesis
    · subst hg
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    have hak : x.stepBefore a ≤ kp := by
      rw [hkp]; exact (stepBefore_mono M) x R E (show a ≤ t by omega)
    have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E p hak) hsel
    exact block_at_tick_of_held_step M F U S A x R GST c t kp a c c₂ kR k₂ p w Y
      (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htR hRoots) hParent hGSTa
      (by omega) hcu le_rfl hv₀ hkpt hpk hY hFa hg hkR hwin hk₂ hc₂ (hslot Y hY) hc
  -- `w`'s finalized block is the finalized block of some held block's chain
  obtain ⟨Bw, hBw, hFw⟩ := (finalizedFromChain_of_exec M F) S A x R E kR w
  have hBwh : (M.chainStateOf S.C Bw).h ≤ hMax M S.C (x.st kR w) := hCacheW Bw hBw
  have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Bw Bw).1
  -- a block `p` holds at a chain-state height at least `w`'s greatest chain-state height is on
  -- `w`'s finalized block's chain (Lemma 89a)
  have hpast : ∀ Y ∈ (x.st kp p).tree,
      hMax M S.C (x.st kR w) ≤ (M.chainStateOf S.C Y).h →
      (x.st kR w).finalized.AncestorEq Y := by
    intro Y hY hYh
    have hlt : (M.chainStateOf S.C Bw).h_F < (M.chainStateOf S.C Y).h :=
      lt_of_le_of_lt h47.2.2 (lt_of_lt_of_le h47.2.1 (le_trans hBwh hYh))
    have hFY := (lem68_honest_past_finalized M F Fx) S A x R E hRoots kR kp w p Bw Y hThird hwk hpk
      hBw hY hlt (max_le htR hkpR')
    rw [hFw]
    exact hFY
  -- step A: `p`'s greatest chain-state height is at most `w`'s
  obtain ⟨⟨Dp, hDpT, hDpJ, hDpj⟩, ⟨X, hXT, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kp p
  obtain ⟨⟨Dw, hDwT, hDwJ, hDwj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kR w
  have hm : hMax M S.C (x.st kp p) ≤ hMax M S.C (x.st kR w) := by
    by_contra hcon
    have hcon' : hMax M S.C (x.st kR w) < (M.chainStateOf S.C X).h := by
      rw [hXh]
      exact Nat.lt_of_not_le hcon
    have hFX := hpast X hXT (le_of_lt hcon')
    -- `X`, of the greatest chain-state height in `p`'s tree, descends from `p`'s finalized block
    have hFpX : (x.st kp p).finalized.AncestorEq X :=
      (hMax_witness_compatible_finalized M F Fx) x R E hRootsT kp p X (hAdv.mono hkpR) hpk hXT
        (fun B hB => by
          rw [hXh]
          exact GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hB) hkpt
    have hXw := hreach X hXT ((compatible_iff _ _).2 (Or.inl hFpX)) ((compatible_iff _ _).2 (Or.inl hFX))
    have h2 : (M.chainStateOf S.C X).h ≤ hMax M S.C (x.st kR w) := hCacheW X hXw
    exact absurd h2 (Nat.not_le.2 hcon')
  have hfw := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.st kR w) hInvW
  have key1 : ∀ a b c : ℕ, a ≤ b → b ≤ c + 1 → a - 1 ≤ c := by intros; omega
  have key2 : ∀ a b c : ℕ, a < b → b ≤ c + 1 → a ≤ c := by intros; omega
  have key3 : ∀ a m hj bj bh hm : ℕ, a = m - 1 → a ≤ hj → hj = bj → bj < bh → bh ≤ hm →
      hm = m → hj = m - 1 := by intros; omega
  have key4 : ∀ m hj hm : ℕ, hm = m → hj = m - 1 → 1 ≤ m - 1 → hm = hj + 1 := by intros; omega
  -- step B: by `p`'s box
  cases hcp : M.fg_contest (x.st kp p) with
  | false =>
      have hfloor : M.head_height_floor (x.st kp p) = hMax M S.C (x.st kp p) - 1 := by
        exact (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
          (x.st kp p) hInvP hcp
      rw [hfloor]
      exact key1 _ _ _ hm hfw
  | true =>
      obtain ⟨hbox, -, hfloor⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X
          (x.st kp p) hInvP hcp
      rw [hfloor]
      -- the block that makes `p` contested
      obtain ⟨-, B', hB'T, hFB', hB'h, hJB'⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X
        (x.st kp p) hInvP hcp
      rcases Nat.lt_or_ge (hMax M S.C (x.st kp p)) (hMax M S.C (x.st kR w)) with hlt | hge
      · exact key2 _ _ _ hlt hfw
      have heq : hMax M S.C (x.st kR w) = hMax M S.C (x.st kp p) := le_antisymm hge hm
      have hFwB' : (x.st kR w).finalized.AncestorEq B' :=
        hpast B' hB'T (by
          show hMax M S.C (x.st kR w) ≤ (M.chainStateOf S.C B').h
          rw [heq, hB'h])
      have hB'w := hreach B' hB'T ((compatible_iff _ _).2 (Or.inl hFB')) ((compatible_iff _ _).2 (Or.inl hFwB'))
      -- `p`'s justified block is justified at its greatest chain-state height minus one, at least `1`
      have hjp : (M.chainStateOf S.C Dp).h_j = hMax M S.C (x.st kp p) - 1 := by
        rw [← hDpj, hbox, Nat.add_sub_cancel]
      have hj1 : 1 ≤ (M.chainStateOf S.C Dp).h_j := by
        rcases Nat.eq_zero_or_pos (M.chainStateOf S.C Dp).h_j with h0 | hpos
        · exfalso
          have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Dp).2.1 h0
          rw [← hDpJ] at hg
          rw [hg] at hJB'
          exact hJB' (genesis_ancestorEq _)
        · exact hpos
      -- `Dp` reaches `w`, so `w`'s justification height is at least that height minus one
      have hDp47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dp Dp).1.2.1
      have hFwDp : (x.st kR w).finalized.AncestorEq Dp :=
        hpast Dp hDpT (by rw [heq]; unfold Height at *; omega)
      have hFpJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E kp p
      have hJDp := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Dp).1
      rw [← hDpJ] at hJDp
      have hDpw := hreach Dp hDpT ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFpJ hJDp)))
        ((compatible_iff _ _).2 (Or.inl hFwDp))
      have hjw1 := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR w Dp
        hDpw hFwDp
      -- and at most that height minus one
      have hDwh := hCacheW Dw hDwT
      have h47w := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dw Dw).1.2.1
      have hjw : (x.st kR w).justifiedHeight = hMax M S.C (x.st kp p) - 1 :=
        key3 _ _ _ _ _ _ hjp hjw1 hDwj h47w hDwh heq
      -- the two justified blocks are one block
      have hcertP := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dp).1 hj1).1
      have hjj : (M.chainStateOf S.C Dw).h_j = (M.chainStateOf S.C Dp).h_j :=
        hDwj.symm.trans (hjw.trans hjp.symm)
      have hj1w : 1 ≤ (M.chainStateOf S.C Dw).h_j := hjj ▸ hj1
      have hcertW := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dw).1 hj1w).1
      rw [hjj] at hcertW
      have hroots := (lem76_honest_one_justification M F Fx) S A x R E kR kp w p hThird Dw Dp hDwT hDpT
        _ _ _ hcertW hcertP
      have hJwT := ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E kR w).2.2.1
      have hJpT := ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E kp p).2.2.1
      have hJJ : (x.st kR w).justified = (x.st kp p).justified := by
        rw [hDwJ, hDpJ]
        refine hRoots _ _
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hwk htR ?_)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hpk hkpR' ?_) hroots
        · rw [← hDwJ]
          exact hJwT
        · rw [← hDpJ]
          exact hJpT
      -- `w` is contested by `B'`
      have hcw : M.fg_contest (x.st kR w) = true := by
        refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X
          (x.st kR w) hInvW B' (key4 _ _ _ heq hjw (hjp ▸ hj1)) hB'w hFwB' ?_ ?_
        · show (M.chainStateOf S.C B').h = _
          rw [heq]
          exact hB'h
        · rw [hJJ]
          exact hJB'
      obtain ⟨-, -, hfloorw⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X
          (x.st kR w) hInvW hcw
      rw [hfloorw, heq]

/-- **`floor_le_of_delivery` read at both validators' ticks** (F-P1-30-4; the holder read as the receiver is, rule R3).
The holder `p` ticks to `cp` at the step `kp`, at a real time at least `a`, and is active from `a` through the sync delay
after it; the receiver `w` ticks to `c`, at least `cp + Δ S`, at the step `kR`, is active at every step from the real
time `a` up to that tick, and ticked earlier to `c₂`, at least the start of the slot of every block `p` holds at its
tick and one delay before `c`; the delivery premises reach `tE`, at least `c`. Then `p`'s `head_height_floor` at
its tick is at most `w`'s at its tick.

Why: as `floor_le_of_delivery_tick`, with `p`'s blocks at its tick delivered by `w`'s tick
(`block_at_tick_of_held_tick`: `p`'s tick is at most `ΔClockBehind` after `cp`, `w`'s at least `ΔClockAhead` before
`c`), and `p`'s finalized block at its tick before its block of greatest chain-state height (Lemma 68 at `p` itself).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from which the network
  is synchronous; `cp`, `kp`: the clock value and the step of `p`'s tick; `a`: the start of the windows; `c`, `kR`:
  the clock value and the step of `w`'s tick; `c₂`, `k₂`: those of its earlier tick; `p`, `w`: the holder and the
  receiver.

Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: the `head_height_floor` of an honest validator at its tick is at most that of another, read at its tick
to a clock value one delay later. -/
theorem floor_le_of_delivery_ticks (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST cp kp a c c₂ kR k₂ : ℕ) (p w : V)
    {tE : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks tE) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST tE)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a third of the validators have been in the adversary set up to the real time of `kR`
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kR))
    -- from `a` on, one delay or one sync delay before `c`, the network is synchronous
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ c)
    -- the holder `p`'s tick to `cp`, at a real time at least `a`; `p` active from `a` through the sync delay after it
    (hkp : x.lbl kp = Event.tick p cp) (hak : (a : ℝ) ≤ x.time kp)
    (hv₀ : p ∈ A.activeThroughout x a (a + Δs))
    -- the receiver `w`'s tick to `c`, at least one delay after `cp`, and its window from `a`
    (hkR : x.lbl kR = Event.tick w c) (hcu : cp + Δ S ≤ c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    -- an earlier tick of `w` to `c₂`, one delay before `c`, at least the start of every slot of `p`'s blocks
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.st kp p).tree, M.slotStart S.C Y.slot ≤ c₂)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : x.time kR ≤ tR)
    -- the delivery premises reach the clock value of the receiver's tick
    (htE : c ≤ tE) :
    M.head_height_floor (x.st kp p) ≤ M.head_height_floor (x.st kR w) := by
  -- `floor_le_of_delivery_tick`'s proof, with `p` read at its tick `kp` (rule R3) and its blocks delivered by `w`'s tick
  -- (`block_at_tick_of_held_tick`) (F-P1-30-4)
  classical
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hpk : p ∉ A.corrupted kp := E.not_mem_corrupted_of_tick hkp
  have hkpt := (E.tick_active kp p cp hkp).2.2
  have hwk : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hcuR : (cp : ℝ) + Δ S ≤ (c : ℝ) := by exact_mod_cast hcu
  have hkpR : x.time kp ≤ x.time kR := by linarith
  have hkpR' : x.time kp ≤ tR := hkpR.trans htR
  have hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (max (x.time kR) (x.time kp)) :=
    hAdv.mono (max_le le_rfl hkpR)
  -- the invariants of the two states
  have hInvP := (lem11_node_invariant M F S A x R E kp p hpk).1
  have hInvW := (lem11_node_invariant M F S A x R E kR w hwk).1
  have hCacheW : GoldilocksCorrectness.Record.Statements.Routines.HeightCacheBounds M S.C (x.st kR w) :=
    fun _ hB => GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hB
  -- every block `p` holds at `kp` (compatible with its finalized block there) that is compatible with `w`'s
  -- finalized block at `kR` reaches `w` by its tick `kR`
  have hreach : ∀ Y ∈ (x.st kp p).tree,
      (x.st kp p).finalized.compatible Y = true →
      (x.st kR w).finalized.compatible Y = true →
      Y ∈ (x.st kR w).tree := by
    intro Y hY hsel hc
    by_cases hg : Y = Block.genesis
    · subst hg
      exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ w
    have hak' : x.stepBefore a ≤ kp := by
      rcases Nat.eq_zero_or_pos a with h0 | h1
      · subst h0; rw [(stepBefore_zero M) x R]; exact Nat.zero_le _
      · exact ((stepBefore_lt_of_le_time M) x R E h1 hak).le
    have hFa := GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
      ((F_ancestorEq_of_le M F) x R E p hak') hsel
    exact block_at_tick_of_held_tick M F U S A x R GST tE cp kp a c c₂ kR k₂ p w Y
      E hNet hSkew hRedeliver Sy
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htR hRoots) hParent hGSTa
      ha hcu htE hv₀ hkp hY hFa hg hkR hwin hk₂ hc₂ (hslot Y hY) hc
  -- `w`'s finalized block is the finalized block of some held block's chain
  obtain ⟨Bw, hBw, hFw⟩ := (finalizedFromChain_of_exec M F) S A x R E kR w
  have hBwh : (M.chainStateOf S.C Bw).h ≤ hMax M S.C (x.st kR w) := hCacheW Bw hBw
  have h47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Bw Bw).1
  -- a block `p` holds at a chain-state height at least `w`'s greatest chain-state height is on
  -- `w`'s finalized block's chain (Lemma 89a)
  have hpast : ∀ Y ∈ (x.st kp p).tree,
      hMax M S.C (x.st kR w) ≤ (M.chainStateOf S.C Y).h →
      (x.st kR w).finalized.AncestorEq Y := by
    intro Y hY hYh
    have hlt : (M.chainStateOf S.C Bw).h_F < (M.chainStateOf S.C Y).h :=
      lt_of_le_of_lt h47.2.2 (lt_of_lt_of_le h47.2.1 (le_trans hBwh hYh))
    have hFY := (lem68_honest_past_finalized M F Fx) S A x R E hRoots kR kp w p Bw Y hThird hwk hpk
      hBw hY hlt (max_le htR hkpR')
    rw [hFw]
    exact hFY
  -- step A: `p`'s greatest chain-state height is at most `w`'s
  obtain ⟨⟨Dp, hDpT, hDpJ, hDpj⟩, ⟨X, hXT, hXh⟩, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kp p
  obtain ⟨⟨Dw, hDwT, hDwJ, hDwj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kR w
  have hm : hMax M S.C (x.st kp p) ≤ hMax M S.C (x.st kR w) := by
    by_contra hcon
    have hcon' : hMax M S.C (x.st kR w) < (M.chainStateOf S.C X).h := by
      rw [hXh]
      exact Nat.lt_of_not_le hcon
    have hFX := hpast X hXT (le_of_lt hcon')
    -- `X`, of the greatest chain-state height in `p`'s tree, descends from `p`'s finalized block
    have hFpX : (x.st kp p).finalized.AncestorEq X := by
      -- `hMax_witness_compatible_finalized`'s proof, with the roots read up to the real time `tR`
      obtain ⟨Bp, hBp, hFBp⟩ := (finalizedFromChain_of_exec M F) S A x R E kp p
      have h47p := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Bp Bp).1
      have hltp : (M.chainStateOf S.C Bp).h_F < (M.chainStateOf S.C X).h :=
        lt_of_lt_of_le (lt_of_le_of_lt h47p.2.2 h47p.2.1)
          (by rw [hXh]; exact GoldilocksCorrectness.Record.Statements.Routines.le_hMax M hBp)
      rw [hFBp]
      exact (lem68_honest_past_finalized M F Fx) S A x R E hRoots kp kp p p Bp X
        (by rw [max_self]; exact hAdv.mono hkpR) hpk hpk hBp hXT hltp (by rw [max_self]; exact hkpR')
    have hXw := hreach X hXT ((compatible_iff _ _).2 (Or.inl hFpX)) ((compatible_iff _ _).2 (Or.inl hFX))
    have h2 : (M.chainStateOf S.C X).h ≤ hMax M S.C (x.st kR w) := hCacheW X hXw
    exact absurd h2 (Nat.not_le.2 hcon')
  have hfw := (GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_floor_add_one M F) S.C S.P S.X
    (x.st kR w) hInvW
  have key1 : ∀ a b c : ℕ, a ≤ b → b ≤ c + 1 → a - 1 ≤ c := by intros; omega
  have key2 : ∀ a b c : ℕ, a < b → b ≤ c + 1 → a ≤ c := by intros; omega
  have key3 : ∀ a m hj bj bh hm : ℕ, a = m - 1 → a ≤ hj → hj = bj → bj < bh → bh ≤ hm →
      hm = m → hj = m - 1 := by intros; omega
  have key4 : ∀ m hj hm : ℕ, hm = m → hj = m - 1 → 1 ≤ m - 1 → hm = hj + 1 := by intros; omega
  -- step B: by `p`'s box
  cases hcp : M.fg_contest (x.st kp p) with
  | false =>
      have hfloor : M.head_height_floor (x.st kp p) = hMax M S.C (x.st kp p) - 1 := by
        exact (GoldilocksCorrectness.Record.Proofs.Routines.head_height_floor_of_not_contested M F) S.C S.P S.X
          (x.st kp p) hInvP hcp
      rw [hfloor]
      exact key1 _ _ _ hm hfw
  | true =>
      obtain ⟨hbox, -, hfloor⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X
          (x.st kp p) hInvP hcp
      rw [hfloor]
      -- the block that makes `p` contested
      obtain ⟨-, B', hB'T, hFB', hB'h, hJB'⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_spec M F) S.C S.P S.X
        (x.st kp p) hInvP hcp
      rcases Nat.lt_or_ge (hMax M S.C (x.st kp p)) (hMax M S.C (x.st kR w)) with hlt | hge
      · exact key2 _ _ _ hlt hfw
      have heq : hMax M S.C (x.st kR w) = hMax M S.C (x.st kp p) := le_antisymm hge hm
      have hFwB' : (x.st kR w).finalized.AncestorEq B' :=
        hpast B' hB'T (by
          show hMax M S.C (x.st kR w) ≤ (M.chainStateOf S.C B').h
          rw [heq, hB'h])
      have hB'w := hreach B' hB'T ((compatible_iff _ _).2 (Or.inl hFB')) ((compatible_iff _ _).2 (Or.inl hFwB'))
      -- `p`'s justified block is justified at its greatest chain-state height minus one, at least `1`
      have hjp : (M.chainStateOf S.C Dp).h_j = hMax M S.C (x.st kp p) - 1 := by
        rw [← hDpj, hbox, Nat.add_sub_cancel]
      have hj1 : 1 ≤ (M.chainStateOf S.C Dp).h_j := by
        rcases Nat.eq_zero_or_pos (M.chainStateOf S.C Dp).h_j with h0 | hpos
        · exfalso
          have hg := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Dp).2.1 h0
          rw [← hDpJ] at hg
          rw [hg] at hJB'
          exact hJB' (genesis_ancestorEq _)
        · exact hpos
      -- `Dp` reaches `w`, so `w`'s justification height is at least that height minus one
      have hDp47 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dp Dp).1.2.1
      have hFwDp : (x.st kR w).finalized.AncestorEq Dp :=
        hpast Dp hDpT (by rw [heq]; unfold Height at *; omega)
      have hFpJ := (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_J_of_exec M F) S A x R E kp p
      have hJDp := ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C Dp).1
      rw [← hDpJ] at hJDp
      have hDpw := hreach Dp hDpT ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFpJ hJDp)))
        ((compatible_iff _ _).2 (Or.inl hFwDp))
      have hjw1 := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E kR w Dp
        hDpw hFwDp
      -- and at most that height minus one
      have hDwh := hCacheW Dw hDwT
      have h47w := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C Dw Dw).1.2.1
      have hjw : (x.st kR w).justifiedHeight = hMax M S.C (x.st kp p) - 1 :=
        key3 _ _ _ _ _ _ hjp hjw1 hDwj h47w hDwh heq
      -- the two justified blocks are one block
      have hcertP := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dp).1 hj1).1
      have hjj : (M.chainStateOf S.C Dw).h_j = (M.chainStateOf S.C Dp).h_j :=
        hDwj.symm.trans (hjw.trans hjp.symm)
      have hj1w : 1 ≤ (M.chainStateOf S.C Dw).h_j := hjj ▸ hj1
      have hcertW := (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C Dw).1 hj1w).1
      rw [hjj] at hcertW
      have hroots := (lem76_honest_one_justification M F Fx) S A x R E kR kp w p hThird Dw Dp hDwT hDpT
        _ _ _ hcertW hcertP
      have hJwT := ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E kR w).2.2.1
      have hJpT := ((GoldilocksCorrectness.Record.Statements.Executions.lem57_justification_cache_and_record M F) S A x R E kp p).2.2.1
      have hJJ : (x.st kR w).justified = (x.st kp p).justified := by
        rw [hDwJ, hDpJ]
        refine hRoots _ _
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hwk htR ?_)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E hpk hkpR' ?_) hroots
        · rw [← hDwJ]
          exact hJwT
        · rw [← hDpJ]
          exact hJpT
      -- `w` is contested by `B'`
      have hcw : M.fg_contest (x.st kR w) = true := by
        refine (GoldilocksCorrectness.Record.Proofs.Routines.fg_contest_true_of M F) S.C S.P S.X
          (x.st kR w) hInvW B' (key4 _ _ _ heq hjw (hjp ▸ hj1)) hB'w hFwB' ?_ ?_
        · show (M.chainStateOf S.C B').h = _
          rw [heq]
          exact hB'h
        · rw [hJJ]
          exact hJB'
      obtain ⟨-, -, hfloorw⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.frameShape_of_boxThree M F) S.C S.P S.X
          (x.st kR w) hInvW hcw
      rw [hfloorw, heq]

/-- **A content of a validator's record in its tick input to the support cutoff of slot `s + 1` is in its record
before the real time of that cutoff (F-P1-29-2)**, when a tick to a clock value at most the support cutoff of slot `s`
happens before that real time.

Why: the content was put on the wire by an earlier tick of the validator, to a clock value less than the support
cutoff of slot `s + 1` (`record_content_sent`); an attestation is sent only at a tick to a support cutoff
(`attest_tick_update_source`), so that clock value is the support cutoff of a slot before `s + 1`, at most the
support cutoff of slot `s`; that tick is at a real time at most the clock value plus `ΔClockBehind`
(`tick_active`), before the real time of the support cutoff of slot `s + 1` by `hB`, so it comes before
`x.stepBefore` of that real time (`lt_stepBefore_of_not_other`); the tick writes the content
(`attest_sent_recorded`) and the record keeps it (`record_sent_mono`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the environment's facts;
- `s`: the slot; `u`: the validator; `b`: the content.

Read aloud: when a tick to a clock value at most the support cutoff of slot `s` happens before the real time of
the support cutoff of slot `s + 1`, every content of a validator's record in its tick input to the support cutoff of
slot `s + 1` is in its record before the real time of that cutoff. -/
theorem record_tickInput_cutoff_mem_stateBefore (U : UniformSchedule M.toSlotLayout) (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {u : V} {b : AttestationContent}
    -- a tick to a clock value at most the support cutoff of slot `s` happens before the real time of the support
    -- cutoff of slot `s + 1`
    (hB : ((M.supportCutoff S.C s : ℕ) : ℝ) + ΔClockBehind < ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ))
    (hb : b ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).sentAttestations) :
    b ∈ (x.stateBefore (M.supportCutoff S.C (s + 1)) u).sentAttestations := by
  obtain ⟨j, t', a, hl, hlt, -, hsent, -, hab, -⟩ := (record_content_sent M F) S A x R _ u b E hb
  obtain ⟨s', -, -, ht', -⟩ := (attest_tick_update_source M F U) S A x R j t' u a E hl hsent
  -- the clock value of the attestation's tick is the support cutoff of a slot before `s + 1`
  have hss : s' < s := by
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s + 1 ≤ s' + 1 by omega)
    omega
  have hle : t' ≤ M.supportCutoff S.C s := by
    rw [ht']
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
      (show s' + 1 ≤ s by omega)
  -- its real time is before the support cutoff of slot `s + 1`
  have htj := (E.tick_active j u t' hl).2.2
  have hle' : (t' : ℝ) ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by exact_mod_cast hle
  have hj : j < x.stepBefore (M.supportCutoff S.C (s + 1)) :=
    (lt_stepBefore_of_not_other M) x R E (by rw [hl]; exact nofun) (by linarith)
  have hrec := (attest_sent_recorded M F) x R E hl hsent
  rw [hab] at hrec
  exact (record_sent_mono M F) x R E u hj hrec

/-- **A viable head of the receiver at its tick bounds the holder's `head_height_floor`**. Under the hypotheses of
`floor_le_of_delivery_tick`: when `W` is a viable head of `w`'s frame at its tick `kR`, `p`'s `head_height_floor`
before `t` is at most `W`'s chain-state height.

Why: `floor_le_of_delivery_tick`, and a viable head is at a chain-state height at least `head_height_floor`
(`mem_viable_heads_iff_of_core`, with the node invariant at `kR`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- the others: as `floor_le_of_delivery_tick`; `W`: the block.

Roots name blocks until `tR`, at least the real time of `kR`.

Read aloud: the `head_height_floor` of an honest validator before a time is at most the chain-state height of any
viable head of another, read at its tick one delay later. -/
theorem floor_le_of_viable_tick (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t a c c₂ kR k₂ : ℕ) (p w : V) (W : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    {tR : ℝ} (hRoots : RootsNameBlocksUntil M A x tR)
    (hParent : ParentHeldAtDelivery M x)
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time kR))
    (hGSTa : GST ≤ a) (ha : a + max (Δ S) Δs ≤ t + Δ S)
    (hv₀ : p ∈ A.activeThroughout x a (a + Δs)) (hp : p ∉ A.corruptedAtTime x t)
    (hkR : x.lbl kR = Event.tick w c) (hcu : t + Δ S ≤ c)
    (hwin : ∀ i : ℕ, (a : ℝ) ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : c₂ + Δ S ≤ c)
    (hslot : ∀ Y ∈ (x.stateBefore t p).tree, M.slotStart S.C Y.slot ≤ c₂)
    (hW : W ∈ (M.fg_to_ac (x.st kR w)).viable_heads)
    (htR : x.time kR ≤ tR) :
    M.head_height_floor (x.stateBefore t p) ≤ (M.chainStateOf S.C W).h := by
  have h := (floor_le_of_delivery_tick M F U Fx) S A x R GST t a c c₂ kR k₂ p w E hNet hSkew hRedeliver Sy hRoots
    hParent hAdv hGSTa ha hv₀ hp hkR hcu hwin hk₂ hc₂ hslot htR
  obtain ⟨-, -, -, hfl⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _
    (show M.nodeInvCore S.C S.P S.X (x.st kR w) from (lem11_node_invariantCore_of_run M F S x R kR w).1) W).1 hW
  exact le_trans h hfl

/-! ## An honest vote and the viable blocks of its voter -/

/-- **The anchor of a frame at a step has a viable head as a descendant.** For every step `i`, every
validator `p` (one in the adversary set included), every finite set of lock entries `E` and every time
`t'`, some block `W` of the tree of `x.st i p` is the anchor `AnchorAt` over `p`'s frame with `E` at
`t'` or a descendant of it, has the fork-choice root of `x.st i p` as an ancestor or is it, and has a
chain-state height at least `head_height_floor` of `x.st i p` (the least chain-state height a viable
block may have). The step form of `anchor_has_viable_head`, which reads the state before a time.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `i`: the step; `p`: the validator; `E`: the
  lock entries; `t'`: the time of the anchor.

Read aloud: at every step, the anchor of a validator's frame is an ancestor of, or equal to, a viable
head of that frame. -/
theorem anchor_has_viable_head_st (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (Env : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (p : V) (E : Finset M.LE) (t' : Time) :
    ∃ W ∈ (x.st i p).tree,
      (AnchorAt M (M.fg_to_ac (x.st i p)) E t').AncestorEq W ∧
      (M.get_fc_root (x.st i p)).AncestorEq W ∧
      M.head_height_floor (x.st i p) ≤ (M.chainStateOf S.C W).h := by
  have hInv := (lem11_node_invariantCore_of_run M F S x R i p).1
  have hvh : ∀ W ∈ (M.fg_to_ac (x.st i p)).viable_heads,
      W ∈ (x.st i p).tree ∧ (M.get_fc_root (x.st i p)).AncestorEq W ∧
      M.head_height_floor (x.st i p) ≤ (M.chainStateOf S.C W).h := by
    intro W hW
    obtain ⟨hT, -, hR, hfl⟩ :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff_of_core M F) S.C S.P S.X _ hInv W).1 hW
    exact ⟨hT, by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hR, hfl⟩
  -- the anchor over `p`'s frame with the lock entries `E` is its fgroot or a block of its viable tree
  rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
      (M.fg_to_ac (x.st i p)) E t' with h | h
  · obtain ⟨W, hW⟩ := (frame_has_viable_head_st M F) S A x R Env i p
    obtain ⟨hT, hR, hfl⟩ := hvh W hW
    refine ⟨W, hT, ?_, hR, hfl⟩
    rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact hR
  · rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F)] at h
    obtain ⟨-, -, W, hW, hAW⟩ := h
    obtain ⟨hT, hR, hfl⟩ := hvh W (Finset.mem_inter.1 hW).2
    exact ⟨W, hT, hAW, hR, hfl⟩


/-- **An honest vote is for an ancestor of a viable block of its voter.** When `u`'s tick at the
vote time of slot `s'` put `vote` on the wire, `vote` is `u`'s slot-`s'` vote for a block `H_u`
that `u` holds before the vote time, and some viable head `W` of `u`'s frame then is `H_u` or a
descendant of `H_u`.

Why: the vote names the end of the Goldfish fork choice from the anchor through the viable tree of
the voter's tree (Lemma 14); a block of that tree is an ancestor of one of its viable heads by
definition, and the anchor is the root or a block of the viable tree of the frame's tree
(`anchor_has_viable_head`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote.

Read aloud: an honest Goldfish vote is for a held block that is an ancestor of a viable head of its
voter or that head. -/
theorem honest_vote_ancestor_of_viable (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s' : ℕ) (u : V) (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧
      ∃ W ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))).viable_heads,
        H_u.AncestorEq W := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hΔ := one_le_Δ S
  have hv₃ : M.voteTime S.C s' = M.slotStart S.C s' + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hss : M.slotStart S.C (s' + 1) = M.slotStart S.C s' + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add,
      Nat.mul_one]
  have hslot : S.C.slot ((M.voteTime S.C s' : ℕ) : Int) = s' := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega)
      (by omega)
  obtain ⟨i, hl, hm⟩ := hSend
  obtain ⟨-, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  -- the tick reads `u`'s state at its step `i`, where `u` is outside the adversary set (it ticks)
  have hTI_i : x.tickInput u (M.voteTime S.C s') = x.st i u := by
    show x.st (x.tickStep u (M.voteTime S.C s')) u = x.st i u
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  rw [hTI_i] at hrun ⊢
  have hInv : M.nodeInv S.C S.P S.X (x.st i u) := (lem11_node_invariant M F S A x R E i u hui).1
  -- Lemma 14 over the record (T5, the field `tick_vote_head` of `F.tk3`): the vote is `u`'s, of
  -- slot `s'`, for the end `H_u` of the walk through the viable part of `u`'s voter tree, from the
  -- anchor over `u`'s frame with the lock entries the tick left (`HeadOf`)
  obtain ⟨-, hvi, hvs, -, -, H_u, ⟨votes, support_votes, -, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInv hvote
  have hnv : (x.st i u).v = u := (lem11_node_invariant M F S A x R E i u hui).2.1
  rw [hnv] at hvi
  rw [hslot] at hvs
  have hvote' : vote = GoldfishVote.mk u s' H_u.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `u` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable
  -- tree
  have hmemT : ∀ D ∈ (M.fg_to_ac (x.st i u)).tree, D ∈ (x.st i u).tree :=
    fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
  have hHT : H_u ∈ (x.st i u).tree := by
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.st i u)) n'.lockEntries
          ((M.voteTime S.C s' : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInv]
        split
        · exact F.nd.nodeInv_justifiedInTree hInv
        · exact F.nd.nodeInv_finalized_mem_tree hInv
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _
        H_u).1 h1).1
  refine ⟨H_u, hHT, hvote', ?_⟩
  -- the walk's end is the anchor, which has a viable head of `u`'s frame as a descendant
  -- (`anchor_has_viable_head_st`), or a block of the viable part of the voter's tree, an ancestor of a
  -- viable head by the viable tree's definition
  rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
  · obtain ⟨W, hWT, hAW, hrW, hflW⟩ := (anchor_has_viable_head_st M F) S A x R E i u
      n'.lockEntries ((M.voteTime S.C s' : ℕ) : Int)
    refine ⟨W, ?_, by rw [h]; exact hAW⟩
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInv]
    refine ⟨hWT, ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F)
      S A x R E i u) hrW, by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hrW, hflW⟩
  · obtain ⟨-, -, W, hW, hHW⟩ := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h
    exact ⟨W, (Finset.mem_inter.mp hW).2, hHW⟩

/-! ## An eligible confirmation has an honest supporter -/

/-- **A saved confirmation has an honest supporter.** When the confirmation read on `v`'s node
state right after the support cutoff of slot `σ + 1` is `X`, with `v` awake and honest from the
duty window's start of slot `σ + 1` to that cutoff (`update_state_of_duty`), some member `u` of
`Hs` put on the wire at the vote time of slot `σ` its vote for a block it held, `X` or a
descendant of `X`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `σ`: the slot of the votes; `v`: the updater; `Hs`: the honest voters;
  `X`: the confirmation.

Roots name blocks until the real time of `v`'s tick to the support cutoff of slot `σ + 1`, where its update runs
(rule R3; F-P1-18).

Read aloud: a saved confirmation of an honest validator has an honest supporter. -/
theorem honest_supporter_of_saved (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST σ : ℕ) (v : V) (Hs : Finset V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (σ + 1)))))
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ)
    (hHs : ∀ u ∈ Hs, u ∈ honestActiveAt M S A x σ ∧ u ∈ S.P.committee σ)
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ) <
      2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (M.supportCutoff S.C (σ + 1)))
    (X : Block V)
    (hX : (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some X) :
    ∃ u ∈ Hs, ∃ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) ∧
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C σ)).tree, vote = GoldfishVote.mk u σ H_u.root ∧
        X.AncestorEq H_u := by
  classical
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hv₁ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ
  have hv₃ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hc0 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ
  have hc1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (σ + 1)
  have hvfz := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S σ
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  have hm : max (Δ S) Δs ≤ M.supportCutoff S.C σ := by omega
  have hmR : ((max (Δ S) Δs : ℕ) : ℝ) = max (Δ S : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hcmR : ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ) =
      ((M.supportCutoff S.C σ : ℕ) : ℝ) - max (Δ S : ℝ) (Δs : ℝ) := by
    rw [Nat.cast_sub hm, hmR]
  have hc0R : ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 2 * (Δ S : ℝ) := by
    have : M.supportCutoff S.C σ = 4 * Δ S * σ + 2 * Δ S := by omega
    rw [this]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 6 * (Δ S : ℝ) := by
    have : M.supportCutoff S.C (σ + 1) = 4 * Δ S * σ + 6 * Δ S := by rw [hc1, hv₃, hss1]; ring
    rw [this]; push_cast; ring
  have hvtR : ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + (Δ S : ℝ) := by
    rw [hv₁, hss0]; push_cast; ring
  have hss : M.slotStart S.C (σ + 1) = M.slotStart S.C σ + 4 * Δ S := by
    rw [hss1, hss0, Nat.mul_add, Nat.mul_one]
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hdw0 := duty_window_start_real S σ
  have hdw1 : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (σ : ℝ) + 5 * (Δ S : ℝ) - 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
    rw [duty_window_start_real S (σ + 1)]; push_cast; ring
  have hDk : (0 : ℝ) ≤ (Δ S : ℝ) * (S.C.k : ℝ) := by positivity
  have hΔs' : max (Δ S : ℝ) (Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := hΔs
  -- the tick to the cutoff and the update it runs, from `v`'s tick input
  obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  obtain ⟨n'', sent, hrun, hAw, hsave, -, -, -⟩ := (update_state_of_tick M F U) S A x R σ v E hk
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout F.sched U) S (σ + 1)))
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R σ v n'' sent hrun hAw
  rw [hsave] at hX
  have htk : x.tickStep v (M.supportCutoff S.C (σ + 1)) = k := (tickStep_eq_of_lbl M) x E hk
  have hti : x.tickInput v (M.supportCutoff S.C (σ + 1)) = x.st k v := by
    unfold Trace.tickInput; rw [htk]
  have hvk : v ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  have hkt := (E.tick_active k v _ hk).2.1
  rw [hc1R] at hkt
  -- `v` is active from `max (Δ S) Δs` before the support cutoff of slot `σ` to that cutoff
  have hvW : v ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
      ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) :=
    (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hv
      (by rw [hcmR, hc0R, hdw1]; have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith)
      (by
        have : M.voteTime S.C σ + Δ S + 4 * Δ S = M.supportCutoff S.C (σ + 1) := by omega
        have h' : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) + 4 * Δ S = ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) := by
          exact_mod_cast this
        linarith)
  -- `v` is active from `ΔClockAhead` before the vote time of slot `σ` up to its tick `k`
  obtain ⟨kT, hkT, hwinT⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := ((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead)
    (by rw [hvtR, hdw1]; have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith)
  have hkTk : kT = k := by
    rw [← (tickStep_eq_of_lbl M) x E hkT, (tickStep_eq_of_lbl M) x E hk]
  rw [hkTk] at hwinT
  have hcR : ((M.voteTime S.C σ + Δ S : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 2 * (Δ S : ℝ) := by
    rw [Nat.cast_add, hvtR]; ring
  -- `v`'s tick `kR` to the support cutoff of slot `σ` (`voteTime σ + Δ S`), before `kT`
  obtain ⟨kR, hkR, hkR1, hkR2⟩ := E.tick_of_active (M.voteTime S.C σ + Δ S) (by omega) v fun i h1 h2 => by
    refine hwinT i (by rw [hvtR]; rw [hcR] at h1; linarith) ?_
    exact ((lt_of_time_lt M) x R (by rw [hcR] at h2; linarith)).le
  have hkRk : kR ≤ k := ((lt_of_time_lt M) x R (by rw [hcR] at hkR2; linarith)).le
  -- the supporters' votes
  have hvotes : ∀ u ∈ Hs, ∃ (i : ℕ) (vote : GoldfishVote V),
      x.lbl i = Event.tick u (M.voteTime S.C σ) ∧ vote.val_index = u ∧ vote.slot = σ ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i :=
    fun u hu => (honest_active_votes M F U) S A x R σ u E hSkew (hHs u hu).1 (hHs u hu).2
  choose iv₀ vf₀ hvf₀ using hvotes
  let iv : V → ℕ := fun u => if h : u ∈ Hs then iv₀ u h else 0
  let vf : V → GoldfishVote V := fun u => if h : u ∈ Hs then vf₀ u h else GoldfishVote.mk u σ
    (Block.genesis : Block V).root
  have hvf : ∀ u ∈ Hs, x.lbl (iv u) = Event.tick u (M.voteTime S.C σ) ∧
      (vf u).val_index = u ∧ (vf u).slot = σ ∧
      (⟨u, NamedObject.gfVote (vf u)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (iv u + 1) - x.sent (iv u) := by
    intro u hu
    simp only [iv, vf, dif_pos hu]
    exact hvf₀ u hu
  have hslot : M.slot S.C (M.voteTime S.C σ) = σ :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hcut : ((((M.voteTime S.C σ + Δ S : ℕ) : Int)) : Stamp) =
      ((S.C.t_ σ + 2 * S.C.Δ : Time) : Stamp) := by
    rw [show M.voteTime S.C σ + Δ S = M.supportCutoff S.C σ by omega,
      (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
  have hlt : S.C.t_ σ + 2 * S.C.Δ < S.C.t_ σ + 6 * S.C.Δ :=
    Int.add_lt_add_left (Int.mul_lt_mul_of_pos_right (by decide) S.C.Δ_pos) _
  -- each supporter's vote is in `v`'s pool at its tick input, stamped in time, and the only one of its voter there
  have hpool : ∀ u ∈ Hs, vf u ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ ∧
      (vf u).val_index = u ∧
      (∃ τ : Stamp, (x.tickInput v (M.supportCutoff S.C (σ + 1))).voteStamp (vf u) =
        some τ ∧ τ < ((S.C.t_ σ + 6 * S.C.Δ : Time) : Stamp)) ∧
      ∀ vote' ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ,
        vote'.val_index = u → vote' = vf u := by
    intro u hu
    obtain ⟨hl, hval, hsl, hsent⟩ := hvf u hu
    have huc1 : u ∉ A.corruptedAtTime x (M.supportCutoff S.C (σ + 1)) := fun h =>
      (Finset.mem_sdiff.1 (hHs u hu).1).2 (Finset.mem_union_left _ h)
    have huk : u ∉ A.corrupted k := fun h =>
      (Finset.mem_sdiff.1 (hHs u hu).1).2 (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, k, v, hk, hvk, h⟩))
    have hsent' : (⟨(vf u).val_index, NamedObject.gfVote (vf u)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (iv u + 1) - x.sent (iv u) := by rw [hval]; exact hsent
    have hcomm : (vf u).val_index ∈ S.P.committee (vf u).slot := by
      rw [hval, hsl]; exact (hHs u hu).2
    have hu₀ : (vf u).val_index ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (Δ S) Δs : ℕ) : ℝ)
        ((M.voteTime S.C σ : ℕ) : ℝ) := by
      rw [hval]
      exact (mem_activeThroughout_of_honestActiveAt M F) R E (hHs u hu).1
        (by rw [hcmR, hc0R, hdw0]; have := le_max_left (Δ S : ℝ) (Δs : ℝ); linarith)
        (by rw [hvtR, hc1R]; linarith)
    -- the vote is in `v`'s pool at its tick `kR` to the support cutoff of slot `σ`, from the send
    have hukR : u ∉ A.corrupted kR := Activity.not_mem_corruptedAtTime.1 huc1 kR (by
      rw [hc1R]; rw [hcR] at hkR2; linarith)
    have hlt1 := (E.tick_active _ u _ hl).2
    have heT : x.time (iv u + 1) ≤ ((M.voteTime S.C σ : ℕ) : ℝ) + ΔClockBehind := by
      rw [R.time_keep (iv u) (by rw [hl]; exact nofun)]; exact hlt1.2
    have hpoolR : vf u ∈ M.votesHeldSet (x.st kR v) σ := by
      rcases (pool_vote_at_tick_of_send M F U) S A x R GST σ (M.voteTime S.C σ) (M.voteTime S.C σ + Δ S) u v
          (vf u) (E.upTo _) hNet hSkew hRedeliver (by omega) le_rfl (by
            have hss2 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (σ + 2)
            rw [hss2, Nat.mul_add]; omega) hsl
          (by rw [hval]; exact (hHs u hu).2) (by omega) (by omega) (iv u) hsent
          (E.not_mem_corrupted_of_tick hl) heT (((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead)
          (by have := R.time_le_succ (iv u); linarith [hlt1.1])
          le_rfl
          kR hkR (fun j hj1 hj2 => hwinT j hj1 (hj2.trans hkRk)) with
        h | ⟨v₁, h₁, v₂, h₂, hne, hi₁, hi₂⟩
      · exact h
      · exact absurd ((unique_vote_of_owner_at M F R) E hOwner hukR h₁ h₂ (hi₁.trans hval)
          (hi₂.trans hval)) hne
    have hpool₂ : vf u ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (σ + 1))) σ := by
      rw [hti]; exact (pool_mono M F) x R E v hkRk σ hpoolR
    refine ⟨hpool₂, hval, ?_, fun vote' hv' hi' => ?_⟩
    · -- stamped before the support cutoff of slot `σ + 1` at `v`'s tick to it
      have hpk : vf u ∈ M.votesHeldSet (x.st k v) σ := by rw [← hti]; exact hpool₂
      obtain ⟨τ, hτ, hτlt⟩ := (voteStamp_lt_of_tick_of_active M F) R E hk
        (by rw [hc1]; omega)
        (fun j hj1 hj2 => hwinT j (by rw [hvtR]; rw [hc1R] at hj1; linarith) hj2) hpk
      refine ⟨τ, by rw [hti]; exact hτ, ?_⟩
      have hc6 : (((M.supportCutoff S.C (σ + 1) : ℕ) : Int) : Stamp) =
          ((S.C.t_ σ + 6 * S.C.Δ : Time) : Stamp) := by
        rw [show M.supportCutoff S.C (σ + 1) = (M.voteTime S.C σ + Δ S) + 4 * Δ S by omega]
        have h2 := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
        have h3 : ((((M.voteTime S.C σ + Δ S : ℕ) : Int)) : Stamp) = ((S.C.t_ σ + 2 * S.C.Δ : Time) : Stamp) := hcut
        have h4 : (((M.voteTime S.C σ + Δ S : ℕ) : Int)) = S.C.t_ σ + 2 * S.C.Δ := by exact_mod_cast h3
        have h5 : (((M.voteTime S.C σ + Δ S + 4 * Δ S : ℕ) : Int)) = S.C.t_ σ + 6 * S.C.Δ := by
          rw [Nat.cast_add, h4, Nat.cast_mul, h2]; push_cast; ring
        rw [h5]
      rw [hc6] at hτlt
      exact hτlt
    · rw [hti] at hv' hpool₂
      exact (unique_vote_of_owner_at M F R) E hOwner huk hv' hpool₂ hi' hval
  -- the update's walk ends at a block with the head root of some supporter's vote
  have hRI : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (σ + 1)))).tree := by
    rw [hti]; exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E k v
  obtain ⟨u, hu, H, hH, hr, hXH⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_supporter F) Hs vf
    hRI hpool hVoters hUpdate X hX
  obtain ⟨hl, hval, hsl, hsent⟩ := hvf u hu
  obtain ⟨H_u, hHT, hvote, -⟩ := (honest_vote_spec M F U) S A x R E σ u (vf u) ⟨iv u, hl, hsent⟩
  refine ⟨u, hu, vf u, ⟨iv u, hl, hsent⟩, H_u, hHT, hvote, ?_⟩
  -- the block of `v`'s tree with the vote's head root is `H_u`: both are held by honest validators by `v`'s tick
  have hHv : H ∈ (x.st k v).tree := by
    have := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).1
    rw [hti] at this; exact this
  have htu : x.tickStep u (M.voteTime S.C σ) = iv u := (tickStep_eq_of_lbl M) x E hl
  have hHTu : H_u ∈ (x.st (iv u) u).tree := by
    have := hHT; unfold Trace.tickInput at this; rw [htu] at this; exact this
  have hui : u ∉ A.corrupted (iv u) := E.not_mem_corrupted_of_tick hl
  have hit := (E.tick_active (iv u) u _ hl).2.2
  rw [hvtR] at hit
  have hroot : H.root = H_u.root := by rw [hr, hvote]
  have hHH : H = H_u :=
    hRoots H H_u ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := v) hvk (by rw [htk]) hHv) ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := iv u) (v := u) hui (by rw [htk]; linarith) hHTu) hroot
  rw [← hHH]
  exact hXH

/-- Two blocks an honest validator holds before a time, with one root, are one block (roots name
blocks).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `u`: the validator;
  `H₁`, `H₂`: the blocks.

Roots name blocks until `tR`, at least `t`: the two blocks are held by `u` before `t`.

Read aloud: two blocks an honest validator holds with one root are one block. -/
theorem eq_of_root_eq_held (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR)
      (t : ℕ)
    (u : V)
    (H₁ H₂ : Block V) (hu : u ∉ A.corruptedAtTime x t) (h₁ : H₁ ∈ (x.stateBefore t u).tree)
    (h₂ : H₂ ∈ (x.stateBefore t u).tree) (hr : H₁.root = H₂.root)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t ≤ tR) : H₁ = H₂ := by
  have ht := (time_stepBefore_le M) x R E t
  have hu' : u ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R E hu (by exact_mod_cast ht)
  exact hRoots H₁ H₂ ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := u) hu' (le_trans ht (by exact_mod_cast htR)) h₁)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := u) hu' (le_trans ht (by exact_mod_cast htR)) h₂) hr

/-! ## The `honestActiveAt` row of a slot's members, read as Lemma 89r's body reads them -/

open GoldilocksCorrectness.Record.Statements.AbstractTrace (honestActiveAt activeAt)

/-- An honest active validator of slot `s` is a reader from the protocol's duty window start of slot `s` to its own
tick to the support cutoff of slot `s + 1`.

Read aloud: membership in `honestActiveAt` gives the per-tick activity to the update tick. -/
theorem reader_cut_of_honestActiveAt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.supportCutoff S.C (s + 1)) :=
  E.mem_activeThroughoutToTick_of_awakeThroughoutToTick (Finset.mem_sdiff.1 hv).1

/-- An honest active validator of slot `s` is outside the adversary set at every step whose time is at most the
real time of the support cutoff of slot `s + 1`.

Read aloud: honesty through the cutoff's real time, which covers every other validator's tick to the vote time of
slot `s + 1` and the proposer's tick to the start of slot `s + 1` (both at most the behind bound after their clock
values, less than one delay before the cutoff). -/
theorem not_corrupted_of_honestActiveAt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) {i : ℕ}
    (hi : x.time i ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ)) : v ∉ A.corrupted i := by
  intro hc
  exact (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ (Activity.mem_corruptedAtTime.2 ⟨i, hi, hc⟩))

/-- The wake rule's reader: an honest active validator of slot `s` ticks to the vote time of slot `s`, active up to
that tick from the trace's start or from its own tick to a clock value at most `duty_window_start S.C s`
(`honest_votes_of_window`'s input through `tickInput_awakeSince_of_mem_activeThroughoutToTick`).

Read aloud: the vote tick lies strictly inside the reader to the update tick, with both clock bounds' margins. -/
theorem reader_vote_of_honestActiveAt (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hct1, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hvR : ((M.voteTime S.C s : ℕ) : ℝ) = 4 * Δ S * s + Δ S := by rw [hvt, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + 5 * Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.voteTime S.C s + 5 * Δ S := by omega
    rw [h]; push_cast; ring
  refine (mem_activeThroughoutToTick_of_inside M F) R E (reader_cut_of_honestActiveAt M F E hv) (by omega) ?_ ?_
  · rw [hdw, hvR]; linarith
  · rw [hc1R]; linarith

/-- The round theorem's reader of the last slot's members: an honest active validator of slot `s` is a reader from
`duty_window_start S.C s` to its own tick to the start of slot `s + 1`.

Read aloud: the reader to the start of the next slot follows from the `honestActiveAt` row. -/
theorem reader_slotStart_of_honestActiveAt (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.slotStart S.C (s + 1)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hct1, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hsR : ((M.slotStart S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 4 * Δ S := by rw [hs1, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.slotStart S.C (s + 1) : ℕ) : ℝ) + 2 * Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.slotStart S.C (s + 1) + 2 * Δ S := by omega
    rw [h]; push_cast; ring
  refine (mem_activeThroughoutToTick_of_inside M F) R E (reader_cut_of_honestActiveAt M F E hv) (by omega) ?_ ?_
  · rw [hdw, hsR]; linarith
  · rw [hc1R]; linarith

/-- The lock step's reader (`liveLocksOnFamilyAt_step` at slot `s − 1`, read at the member of slot `s`): an honest
active validator of slot `s` is a reader from the model's duty window start of slot `s + 1` to its own tick to the
vote time of slot `s + 1`.

Read aloud: the reader's start moves later (the protocol's start of slot `s` is at most the model's start of slot
`s + 1`) and its end moves earlier (the vote time of slot `s + 1` lies strictly inside the reader to the cutoff). -/
theorem reader_lock_of_honestActiveAt (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {s : ℕ} {v : V} (hv : v ∈ honestActiveAt M S A x s) :
    v ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s + 1) : ℤ) (M.voteTime S.C (s + 1)) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨hvt1, hct1, -, -, hdc1, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  -- the start: the protocol's duty window start of slot `s` is at most the model's of slot `s + 1`
  have hstart : duty_window_start S.C s ≤ ((M.dutyWindowStart S.C (s + 1) : ℕ) : ℤ) :=
    le_trans ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_le_dutyWindowStart M.toSlotLayout F.sched U) S s)
      (by exact_mod_cast (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_mono M.toSlotLayout F.sched) S (Nat.le_succ s))
  have hrd := Activity.mem_activeThroughoutToTick_of_le hstart (reader_cut_of_honestActiveAt M F E hv)
  -- the end: the vote time of slot `s + 1` lies strictly inside, with the margins
  have hv1R : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * s + 5 * Δ S := by rw [hvt1, hs1, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.voteTime S.C (s + 1) : ℕ) : ℝ) + Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := by omega
    rw [h]; push_cast; ring
  refine (mem_activeThroughoutToTick_of_inside M F) R E hrd (by omega) ?_ ?_
  · -- the model's duty window start of slot `s + 1` is more than both bounds before that vote time
    rcases hdc1 with h | ⟨h0, -⟩
    · have hR : ((M.dutyWindowStart S.C (s + 1) : ℕ) : ℝ) + 4 * Δ S * S.C.k = 4 * Δ S * s + 5 * Δ S := by
        have h' : ((M.dutyWindowStart S.C (s + 1) + 4 * Δ S * S.C.k : ℕ) : ℝ) = ((M.slotStart S.C (s + 1) + Δ S : ℕ) : ℝ) := by rw [h]
        rw [hs1, hss] at h'; push_cast at h'; linarith
      push_cast; rw [hv1R]; linarith
    · have hDs : (0 : ℝ) ≤ 4 * (Δ S : ℝ) * (s : ℝ) := by positivity
      rw [h0]; push_cast; rw [hv1R]; linarith
  · rw [hc1R]; linarith

/-- The body's holder row `hHold` at slot `s` (the real window `[cut(s) − max (2 · Δ S) Δs, … + Δs]`) from the
`honestActiveAt` row, under `hGST` at the support cutoff of slot `s` (which bounds `Δs` by that cutoff, so that the
window's start is not truncated and its end is at most the cutoff).

Read aloud: the window starts after the reader's opening tick (by more than the behind bound) and ends before the
update tick (by more than the ahead bound), so the reader covers it. -/
theorem hold_of_honestActiveAt (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {GST s : ℕ} {v : V}
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s) (hv : v ∈ honestActiveAt M S A x s) :
    v ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  obtain ⟨hvt, hct, -, hs1, -, hk8, hΔ⟩ := (slot_times M F U) S s
  obtain ⟨-, hct1, -, -, -, -, -⟩ := (slot_times M F U) S (s + 1)
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hdw := duty_window_start_real S s
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hk8R : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by exact_mod_cast hk8
  have hm : max (2 * Δ S) Δs ≤ M.supportCutoff S.C s := by omega
  have hmN : max (2 * Δ S) Δs ≤ max (Δ S) Δs + Δ S := by omega
  have hmR : ((max (2 * Δ S) Δs : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) + Δ S := by exact_mod_cast hmN
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = 4 * Δ S * s + 2 * Δ S := by rw [hct, hss]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = ((M.supportCutoff S.C s : ℕ) : ℝ) + 4 * Δ S := by
    have h : M.supportCutoff S.C (s + 1) = M.supportCutoff S.C s + 4 * Δ S := by omega
    rw [h]; push_cast; ring
  have he : (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs) =
      ((M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) := by push_cast; ring
  rw [he]
  refine (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E (reader_cut_of_honestActiveAt M F E hv) ?_ ?_
  · rw [hdw, Nat.cast_sub hm, hcR]
    push_cast at hmR ⊢
    linarith
  · have hle : M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs ≤ M.supportCutoff S.C s := by omega
    have hleR : ((M.supportCutoff S.C s - max (2 * Δ S) Δs + Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C s : ℕ) : ℝ) := by
      exact_mod_cast hle
    rw [hc1R]; linarith

/-- The proposer, outside the adversary set up to the real time of the support
cutoff of slot `s`, is outside it at a member's tick to the vote time of slot `s` (at most the behind bound after that
vote time, less than one delay before the cutoff).

Read aloud: the member's vote tick is before the cutoff's real time, where the proposer is still honest. -/
theorem proposer_honest_at_member_tick (U : UniformSchedule M.toSlotLayout) {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) {s : ℕ} {p w : V}
    (hp : p ∉ A.corruptedAtTime x (M.supportCutoff S.C s)) :
    p ∉ A.corrupted (x.tickStep w (M.voteTime S.C s)) := by
  have hA0 := E.ahead_nonneg
  obtain ⟨hvt, hct, -, -, -, -, hΔ⟩ := (slot_times M F U) S s
  have ht := (time_tickStep_le_add_behind M F) x R E w (M.voteTime S.C s)
  have hcR : ((M.supportCutoff S.C s : ℕ) : ℝ) = ((M.voteTime S.C s : ℕ) : ℝ) + Δ S := by
    have h : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := by omega
    rw [h]; push_cast; ring
  refine (not_mem_corrupted_of_le_time M) x R E hp ?_
  rw [hcR]; linarith

end GoldilocksCorrectness.Record.Proofs.Executions

