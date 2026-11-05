module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Routines.Lemma77
public import GoldilocksCorrectness.Proofs.Routines.Frame
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ConfirmationSupporters
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89Stability, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Stability.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the kit of the stability fact of
Lemma 89 that does not read the fork-choice change, namely the caches of a node state, the finalized
block an ancestor of every honest-held block whose chain-state height is greater than the cache
`h_j`, a block delivered within one delay, the end of an honest Goldfish vote, and a confirmation
saved when a voter majority votes on the chain of the updater's finalized block. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ
  slotStart_eq slot_eq_of_mem supportCutoff_eq viewFreeze_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (VoterTree)

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

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The caches of a node state -/

/-- A held block's chain state in a node state is the block's own (Lemma 11).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `B`: the block.

The record has no chain-state cache in a node state: it reads a held block's chain state as
`M.chainStateOf S.C B` itself, so the landed statement reads, by rename, an equation of that
chain state with itself, and takes no execution, time, validator or holding hypothesis (the
unused hypotheses deleted). The recovery reads the landed equation from Lemma 11 at the spec's
model.

Read aloud: over the record, the chain state of a held block is `M.chainStateOf S.C B` itself, with
no cache to compare it to. -/
theorem σ_eq_of_stateBefore (S : Setup V) (B : Block V) :
    M.chainStateOf S.C B = M.chainStateOf S.C B :=
  rfl

/-- A held block's chain-state height is at most the greatest chain-state height `hMax M S.C n` of
the node state `n` (the landed cache `h_max`, Lemma 46).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator;
  `B`: the block.

Read aloud: a block a node state holds has a chain-state height at most that state's greatest
chain-state height. -/
theorem height_le_h_max (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t : ℕ) (v : V) (B : Block V)
    (hB : B ∈ (x.stateBefore t v).tree) :
    (M.chainStateOf S.C B).h ≤ hMax M S.C (x.stateBefore t v) :=
  le_hMax M hB

/-- The cache `h_j` is less than the greatest chain-state height `hMax M S.C n` of the node state
`n`: the justified block's witness has a chain-state height greater than its justification height
(Lemma 47) and at most `hMax M S.C n`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.

Read aloud: a node state's justification height is less than its greatest chain-state height. -/
theorem h_j_lt_h_max (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    (x.stateBefore t v).justifiedHeight < hMax M S.C (x.stateBefore t v) := by
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t v
  have h1 := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  have h2 := (height_le_h_max M F) S A x t v D hD
  rw [hj]
  exact lt_of_lt_of_le h1 h2

/-- The greatest chain-state height `hMax M S.C n` of a validator's node state `n` does not
decrease: the block witnessing it stays in the tree.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `t ≤ t'`: the
  two times.

Read aloud: a validator's greatest chain-state height does not decrease over time. -/
theorem h_max_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {t t' : ℕ}
    (htt : t ≤ t') :
    hMax M S.C (x.stateBefore t v) ≤ hMax M S.C (x.stateBefore t' v) := by
  obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t v
  rw [← hXh]
  exact (height_le_h_max M F) S A x t' v X (((stateBefore_grows M F) x R E v htt).1 hX)

/-- **The finalized block is an ancestor of every honest-held block higher than the cache `h_j`.**
Under unforgeability, roots naming blocks, permanent corruption and fewer than a third of the
validators in the adversary set up to `tEnd`: when `w` is honest at `t ≤ tEnd`, `p` is honest at
`t' ≤ tEnd` and holds `B` before `t'`, and `B`'s chain-state height is greater than `w`'s cache
`h_j` before `t`, then `w`'s finalized block before `t` is `B` or an ancestor of `B`.

Why: `w`'s finalized block is the finalized block of the chain state of a block `D` it holds
(`finalizedFromChain_of_exec`), at a finalization height at most `D`'s justification height
(Lemma 47), at most `w`'s `h_j` (Lemma 57, `D` being on the finalized block's chain); Lemma 89a.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`: the time up to which the
  adversary bound holds; `t`, `t'`: the two times; `w`, `p`: the two validators; `B`: the block.

Roots name blocks until `tR`, at least `max t t'`: the proof compares (Lemma 89a) a block `w`
holds before `t` with `B`, which `p` holds before `t'`.

Read aloud: an honest validator's finalized block is an ancestor of, or equal to, every block an
honest validator holds whose chain-state height is greater than the first validator's justification
height. -/
theorem F_ancestorEq_of_high (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ}
      (hRoots : RootsNameBlocksUntil M A x tR)
    (tEnd t t' : ℕ) (w p : V) (B : Block V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hw : w ∉ A.corruptedAtTime x t) (hp : p ∉ A.corruptedAtTime x t')
    (hB : B ∈ (x.stateBefore t' p).tree)
    (hlt : (x.stateBefore t w).justifiedHeight < (M.chainStateOf S.C B).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (x.stateBefore t w).finalized.AncestorEq B := by
  obtain ⟨D, hD, hF⟩ := (finalizedFromChain_of_exec M F) S A x R E (x.stepBefore t) w
  have hSt : x.stateBefore t w = x.st (x.stepBefore t) w := rfl
  rw [← hSt] at hD hF
  by_cases h0 : (M.chainStateOf S.C D).h_F = 0
  · rw [hF, (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_F_genesis M F) S.C D h0]
    exact genesis_ancestorEq B
  have hFD : (M.chainStateOf S.C D).F.AncestorEq D :=
    (((GoldilocksCorrectness.Record.Statements.Routines.lem66_chain_state_certified M F) S.C D).2.2
      (Nat.one_le_iff_ne_zero.mpr h0)).2.2.1
  have hjD : (M.chainStateOf S.C D).h_j ≤ (x.stateBefore t w).justifiedHeight :=
    (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_stateBefore M F) S A x R E t w D hD (by rw [hF]; exact hFD)
  have hFj := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.2
  have hlt' : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C B).h :=
    lt_of_le_of_lt hFj (lt_of_le_of_lt hjD hlt)
  have hti := (time_stepBefore_le M) x R E t
  have htj := (time_stepBefore_le M) x R E t'
  have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (x.stepBefore t)) (x.time (x.stepBefore t'))) :=
    hThird.mono (max_le (hti.trans (by exact_mod_cast ht)) (htj.trans (by exact_mod_cast ht')))
  have hw' : w ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R E hw (by exact_mod_cast hti)
  have hp' : p ∉ A.corrupted (x.stepBefore t') :=
    (not_mem_corrupted_of_le_time M) x R E hp (by exact_mod_cast htj)
  have h68 := (lem68_honest_past_finalized M F Fx) S A x R E hRoots (x.stepBefore t)
    (x.stepBefore t') w p D B hT hw' hp' hD hB hlt' (le_trans (max_le_max hti htj) (by exact_mod_cast htR))
  rw [hF]
  exact h68

/-- **The cache `h_j` of an honest validator does not decrease.** Under the assumptions of
`F_ancestorEq_of_high`: when `w` is honest at `t'` and `t ≤ t' ≤ tEnd`, `w`'s cache `h_j` before
`t` is at most its cache `h_j` before `t'`.

Why: the block `D` witnessing the cache before `t` stays in the tree and has a chain-state height
greater than its justification height (Lemma 47); were the later cache smaller, `w`'s later
finalized block would be an ancestor of `D` (`F_ancestorEq_of_high`), and then `D`'s justification
height is at most the later cache (Lemma 57).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`: the time up to which the
  adversary bound holds; `t ≤ t'`: the two times; `w`: the validator.

Roots name blocks until `tR`, at least `t'`: `F_ancestorEq_of_high` at the times `t'` and
`t ≤ t'`.

Read aloud: an honest validator's justification height does not decrease over time. -/
theorem h_j_mono (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    
    {tR : ℕ} (hRoots : RootsNameBlocksUntil M A x tR) (tEnd t t' : ℕ) (w : V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (htt : t ≤ t')
      (ht' : t' ≤ tEnd)
    (hw : w ∉ A.corruptedAtTime x t')
    -- the latest time the proof takes a block as held is at most the bound
    (htR : t' ≤ tR) :
    (x.stateBefore t w).justifiedHeight ≤ (x.stateBefore t' w).justifiedHeight := by
  by_contra hlt
  push Not at hlt
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := (cachesWitnessed_of_stateBefore M F) S A x R E t w
  have hD' : D ∈ (x.stateBefore t' w).tree := ((stateBefore_grows M F) x R E w htt).1 hD
  have hDh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  have hwt : w ∉ A.corruptedAtTime x t := (not_mem_corruptedAtTime_of_le M) x R E (by exact_mod_cast htt) hw
  have hFD := (F_ancestorEq_of_high M F Fx) S A x R E hRoots tEnd t' t w w D hThird ht'
    (le_trans htt ht') hw hwt hD (by rw [hj] at hlt; exact lt_trans hlt hDh)
    (max_le htR (le_trans htt htR))
  have hjD := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_stateBefore M F) S A x R E t' w D hD' hFD
  rw [hj] at hlt
  exact absurd hjD (not_le.mpr hlt)

/-! ## The root and `head_height_floor` (the least chain-state height a viable block may have) of an FG state -/

/-! ## A block delivered within one delay -/

/-- A validator outside the adversary set at `e` is active at every time from `b - c` to `e`, when
every validator outside the adversary set is awake from `a ≤ b - c` through `tEnd ≥ e`.

Why: corruption is permanent (`not_mem_adv_of_le`), so the validator is outside the adversary set at
every earlier time, and awake there by `hAw`.

The variables:
- `M`: the model; `F`: its facts; `E`: the environment's facts (corruption is permanent);
- `a`, `tEnd`: the awake window; `b`, `c`: the window's end and length; `e`: its last time; `w`: the
  validator.

Read aloud: a validator honest at `e` is active through the window ending at `e` that starts inside
the awake window. -/
theorem activeThroughout_of_awake_from {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a tEnd b c e : ℕ} {w : V}
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hw : w ∉ A.corruptedAtTime x e) (hab : a + c ≤ b) (hcb : c ≤ b) (he : e ≤ tEnd) :
    w ∈ A.activeThroughout x (b - c) e := by
  have h := (mem_activeThroughout_of_hAwake_honest_at M F) R E hAw (a := b - c) (by omega) he hw
  rw [Nat.cast_sub hcb] at h
  exact h

/-- A validator outside the adversary set at `e` is active at every time from `b` to `e`, when every
validator outside the adversary set is awake from `a ≤ b` through `tEnd ≥ e` (`activeThroughout_of_awake_from`
with the window's start a natural number).

The variables:
- `M`: the model; `F`: its facts; `E`: the environment's facts (corruption is permanent);
- `a`, `tEnd`: the awake window; `b`, `e`: the window's first and last times; `w`: the validator.

Read aloud: a validator honest at `e` is active from `b` through `e` inside the awake window. -/
theorem activeThroughout_nat_of_awake_from {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {a tEnd b e : ℕ} {w : V}
    (hAw : ∀ (i : ℕ) (v : V), x.time i ≤ tEnd → (a : ℝ) ≤ x.time (i + 1) → v ∉ A.corrupted i → v ∈ A.awake i)
    (hw : w ∉ A.corruptedAtTime x e) (hab : a ≤ b) (he : e ≤ tEnd) :
    w ∈ A.activeThroughout x b e := by
  exact (mem_activeThroughout_of_hAwake_honest_at M F) R E hAw hab he hw

/-! ## The voter's tree -/

/-- **A block held early is in the voter's tree at a later step.** When `w` is outside the adversary set after `i` steps, held `B` at a step
`k ≤ i` at which its clock value is less than the view freeze of slot `s' − 1`, and the finalized
block of `x.st i w` is `B` or an ancestor of `B`, then `B` is in the voter's tree of slot `s'` of
`x.st i w`: `B` stays in the tree with its stamp, which is `w`'s clock value at `B`'s entry, at most
its clock value at `k`.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `k ≤ i`: the two steps; `s'`: the slot of
  the vote; `w`: the voter; `B`: the block.

Read aloud: a block a validator held while its clock was before the view freeze, with the finalized
block an ancestor of it, is in the voter's tree of the slot at every later step. -/
theorem mem_voter_tree_st (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k i s' : ℕ} {w : V} {B : Block V} (hki : k ≤ i) (hw : w ∉ A.corrupted i)
    (hB : B ∈ (x.st k w).tree) (hck : x.clockValue k w < M.viewFreeze S.C (s' - 1))
    (hFB : (x.st i w).finalized.AncestorEq B) :
    B ∈ VoterTree M S.C (x.st i w) s' := by
  have hG := (grows_of_le M F) x R E w hki
  have hT : B ∈ (x.st i w).tree := hG.1 hB
  have hΦ : B ∈ (M.fg_to_ac (x.st i w)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hT, hFB⟩
  have hfz : ((S.C.t_ (s' - 1) + 3 * S.C.Δ : Time) : Stamp) =
      ((((M.viewFreeze S.C (s' - 1) : ℕ) : Int)) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
  refine (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ s' B).2 ⟨hΦ, ?_⟩
  by_cases hg : B = Block.genesis
  · subst hg
    refine ⟨⊥, (genesis_stamp M F) x R E i w, Or.inl ?_⟩
    rw [hfz]
    exact WithBot.bot_lt_coe _
  obtain ⟨e, hek, -, -, hst⟩ := (blockStamp_entry_clock M F R E) hB hg
  have hwk : w ∉ A.corrupted k := E.not_mem_corrupted_of_le hki hw
  have hce : x.clockValue (e + 1) w ≤ x.clockValue k w := E.clockValue_mono (by omega) hwk
  refine ⟨_, by rw [(blockStamp_kept M F) x R E w hki hB]; exact hst, Or.inl ?_⟩
  rw [hfz, (clock_eq_clockValue M F) x R (e + 1) w]
  exact WithBot.coe_lt_coe.2 (by exact_mod_cast lt_of_le_of_lt hce hck)

/-- **The voter's tree at a step holds every block from the fork-choice root to one of its blocks**
(the step form of `voter_tree_closed`): such a block is held (it is an ancestor of a held block), the
finalized block is an ancestor of it, and it was stamped before the view freeze, or leads to a
slot-`s'` block, whenever the block of the tree it is an ancestor of was or does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `i`: the step; `s'`: the slot of the vote;
  `w`: the voter.

Read aloud: at every step, the voter's tree of a slot holds every block between the fork-choice root
and one of its blocks. -/
theorem voter_tree_closed_st (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i s' : ℕ) (w : V) :
    ∀ Z ∈ VoterTree M S.C (x.st i w) s', ∀ c : Block V,
      (M.fg_to_ac (x.st i w)).fc_root.AncestorEq c → c.AncestorEq Z →
      c ∈ VoterTree M S.C (x.st i w) s' := by
  intro Z hZ c hρc hcZ
  have hiff := GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C (x.st i w) s'
  obtain ⟨hZΦ, τ, hτ, hor⟩ := (hiff Z).1 hZ
  have hZT : Z ∈ (x.st i w).tree := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hZΦ).1
  have hcT : c ∈ (x.st i w).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x R E i w Z c hZT hcZ
  have hFc : (x.st i w).finalized.AncestorEq c :=
    ancestorEq_trans ((GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x R E i w)
      (by rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]; exact hρc)
  have hcΦ : c ∈ (M.fg_to_ac (x.st i w)).tree :=
    ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hcT, hFc⟩
  obtain ⟨τc, τZ, hτc, hτZ, hle⟩ := (ancestor_blockStamp_le M F) S A x R E i w Z c hZT hcZ
  rcases hor with hlt | ⟨B', hB', hslot, hZB'⟩
  · -- `Z` was stamped before the view freeze, and so was `c`, its ancestor, stamped no later
    have hτZ' : τZ = τ := Option.some_injective _ (hτZ.symm.trans hτ)
    exact (hiff c).2 ⟨hcΦ, τc, hτc, Or.inl (lt_of_le_of_lt (hτZ' ▸ hle) hlt)⟩
  · exact (hiff c).2 ⟨hcΦ, τc, hτc, Or.inr ⟨B', hB', hslot, ancestorEq_trans hcZ hZB'⟩⟩

/-! ## The end of the Goldfish fork choice -/

/-- The voter's tree of slot `s'` holds every block from the fork-choice root to one of its
blocks: such a block is held (it is an ancestor of a held block), the finalized block is an
ancestor of it, and it was held before the view freeze, or leads to a slot-`s'` block, whenever the
block of the tree it is an ancestor of was or does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot of the vote; `w`: the
  voter.

The landed statement reads `w`'s voter tree as the answer `tree` of `voter_block_tree`; the twin
reads the record's voter's tree `VoterTree M S.C n s'` of `w`'s node state `n` (the shape of
`proposal_viable_head_at`).

Read aloud: the voter's tree of a slot holds every block between the fork-choice root and one of its
blocks. -/
theorem voter_tree_closed (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s' : ℕ) (w : V) :
    ∀ Z ∈ VoterTree M S.C (x.stateBefore (M.voteTime S.C s') w) s', ∀ c : Block V,
      (M.fg_to_ac (x.stateBefore (M.voteTime S.C s') w)).fc_root.AncestorEq c → c.AncestorEq Z →
      c ∈ VoterTree M S.C (x.stateBefore (M.voteTime S.C s') w) s' :=
  -- the state before a time is the state at the step before it
  (voter_tree_closed_st M F U) S A x R E (x.stepBefore (M.voteTime S.C s')) s' w

/-- **An honest vote, its block, and the blocks it extends.** When `u`'s tick at the vote time of
slot `s'` put `vote` on the wire, `vote` is `u`'s slot-`s'` vote for a block `H_u` that `u` holds
before the vote time, `u`'s fork-choice root then is `H_u` or an ancestor of it, and `H_u` is `F'`
or a descendant of `F'` for every block `F'` such that: `u` held, at a step `k` at most its tick at
which its clock value is less than the view freeze of slot `s' − 1`, a block `Y` that is a viable head
of its frame at the tick; every viable head of that frame is `F'` or a descendant of `F'`; and no
strict ancestor of `F'` is a viable head of it. (The voter tree's test reads `Y`'s stamp, `u`'s clock
value when `Y` entered its tree, so the premise is on the clock value, not on a real time.)

Why: the vote names the end of the Goldfish fork choice from the anchor through the viable tree of
the voter's tree (Lemma 14), and the anchor is the root or a descendant of it; `Y` is in the
voter's tree (`mem_voter_tree_st`), which holds every block from the root to one of its
blocks (`voter_tree_closed_st`); and `walk_end_extends`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote.

Read aloud: an honest vote is for a block the voter holds, a descendant of the fork-choice root, and
a descendant of every block the voter held in time with its finalized block an ancestor of it. -/
theorem honest_vote_spec (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s' : ℕ) (u : V) (vote : GoldfishVote V)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree,
      vote = GoldfishVote.mk u s' H_u.root ∧
      (M.get_fc_root (x.tickInput u (M.voteTime S.C s'))).AncestorEq H_u ∧
      ∀ (k : ℕ) (Y F' : Block V), k ≤ x.tickStep u (M.voteTime S.C s') → Y ∈ (x.st k u).tree →
        x.clockValue k u < M.viewFreeze S.C (s' - 1) →
        Y ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))).viable_heads →
        (∀ W ∈ (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))).viable_heads, F'.AncestorEq W) →
        (∀ B : Block V, B.AncestorEq F' → B ≠ F' →
          B ∉ (M.fg_to_ac (x.tickInput u (M.voteTime S.C s'))).viable_heads) →
        F'.AncestorEq H_u := by
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
  have hi : x.tickStep u (M.voteTime S.C s') = i := (tickStep_eq_of_lbl M) x E hl
  have hTI_i : x.tickInput u (M.voteTime S.C s') = x.st i u := by
    show x.st (x.tickStep u (M.voteTime S.C s')) u = x.st i u
    rw [hi]
  have hui : u ∉ A.corrupted i := E.not_mem_corrupted_of_tick hl
  rw [hTI_i] at hrun ⊢
  rw [hi]
  have hInv : M.nodeInv S.C S.P S.X (x.st i u) := (lem11_node_invariant M F S A x R E i u hui).1
  -- Lemma 14 over the record (T5, the field `tick_vote_head` of `F.tk3`): the vote is `u`'s, of
  -- slot `s'`, for the end `H_u` of the walk through the viable part of `u`'s voter tree, from the
  -- anchor over `u`'s frame with the lock entries the tick left (`HeadOf`)
  obtain ⟨-, hvi, hvs, -, -, H_u, ⟨votes, support_votes, -, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInv hvote
  have hnv : (x.st i u).v = u := (lem11_node_invariant M F S A x R E i u hui).2.1
  rw [hnv] at hvi
  rw [hslot] at hvs hWalk
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
  -- the anchor is the fgroot or a descendant of it, and the walk's end is the anchor or a
  -- descendant of it
  have hRA : (M.fg_to_ac (x.st i u)).fc_root.AncestorEq
      (GoldilocksCorrectness.Record.Statements.Routines.AnchorAt M
        (M.fg_to_ac (x.st i u)) n'.lockEntries ((M.voteTime S.C s' : ℕ) : Int)) := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
        (M.fg_to_ac (x.st i u)) n'.lockEntries ((M.voteTime S.C s' : ℕ) : Int) with h | h
    · rw [h]
      exact ancestorEq_refl _
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
  have hRH : (M.get_fc_root (x.st i u)).AncestorEq H_u := by
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F) (x.st i u)]
    exact ancestorEq_trans hRA (GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1)
  refine ⟨H_u, hHT, hvote', hRH, ?_⟩
  -- `Y` is in the voter's tree, which holds every block from the root to one of its blocks
  intro k Y F' hki hYT hck hYv hP hQ
  have hYvbt : Y ∈ VoterTree M S.C (x.st i u) s' :=
    (mem_voter_tree_st M F U) S A x R E hki hui hYT hck
      (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInv Y).1
        hYv).2.1
  exact (GoldilocksCorrectness.Record.Proofs.Routines.walk_end_extends M F) S.C _ _ _ _ votes support_votes
    (s' - 1) H_u F' Y ((voter_tree_closed_st M F U) S A x R E i s' u)
    (GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M _ n'.lockEntries _) hWalk
    (fun W hW => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_heads_iff M F) S.C S.P S.X _ hInv
      W).1 hW).2.2.1) hYvbt hYv hP hQ

/-! ## A confirmation saved -/

/-- **An honest update saves a confirmation when a voter majority votes on the chain of the
updater's finalized block.** Lemma 78's hypotheses with `B` the finalized block of `v` before the
support cutoff `c` of slot `s + 1`: when `GST` is at most the vote time of slot `s`; every member of
`Hs` is in the slot-`s` committee, honest through `c`, sent its slot-`s` vote for `H u`, a block it
holds that is `v`'s finalized block or a descendant of it; the validators with a slot-`s` vote in
`v`'s pool before `c` are fewer than twice `Hs`; and `v` is awake and honest from the duty window's
start of slot `s + 1` to `c` — then `v` holds right after `c` some confirmation of slot `s`.

Why: Lemma 78's first case: Lemma 12 delivers every member's vote to `v`, held early, so each is an
early supporter of `v`'s finalized block, and `update_confirmation_saves`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes; `Hs`: the honest voters; `H`: the block each
  voter's vote is for; `v`: the updater.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: Lemma 12 at slot `s`
(`lem12_honest_vote_delivered_until_of_steps`). The voters are outside the adversary set at `v`'s tick to the support cutoff
of slot `s + 1`, and active through the sync delay after Lemma 12's read time.

Read aloud: an honest update saves a confirmation when a voter majority votes on the chain of the
updater's finalized block. -/
theorem confirmation_saved_of_votes (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧
      (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.AncestorEq (H u))
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' := by
  have hΔ := one_le_Δ S
  have hc₁ : M.supportCutoff S.C s = M.voteTime S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hv₂ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hc₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  -- `v`'s tick to the support cutoff of slot `s + 1`, and the state it reads
  obtain ⟨kc, hkc, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
  have hkcs : x.tickStep v (M.supportCutoff S.C (s + 1)) = kc := (tickStep_eq_of_lbl M) x E hkc
  have hti : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st kc v := by
    unfold Trace.tickInput; rw [hkcs]
  -- an outcome of that tick, the update it ran, and the saved confirmation it leaves
  obtain ⟨n'', sent, hrun, hAwake, hSv, -, -, -⟩ := (update_state_of_tick M F U) S A x R s v E hkc
    ((tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hv
      ((GoldilocksCorrectness.Record.Proofs.Routines.duty_window_start_lt_supportCutoff M.toSlotLayout
        F.sched U) S (s + 1)))
  have hUpdate := (confirmationUpdated_of_cutoff_tickInput M F U) x R s v n'' sent hrun hAwake
  -- Lemma 12 at `v`'s tick: every voter's vote is held early
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s (H u) u :=
    (lem12_honest_vote_delivered_until_of_steps M F U) S A x R GST s (M.supportCutoff S.C (s + 1)) Hs H v
      E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST (by omega) kc hkc
      (fun u hu => ⟨(hHs u hu).1, hkcs ▸ (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
      hHold ((updater_reader_gives_core_window M F U) x R E hΔs hSkew hv)
      (fun u hu => (hHs u hu).2.2.2.2)
  have hRoots₂ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E kc v
  -- every voter is an early supporter of the finalized block
  have hSup : ∀ u ∈ Hs, GoldilocksCorrectness.Record.Statements.Routines.EarlySupporterOf M S.C
      (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1)
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).F u :=
    fun u hu => (heldEarlyVoteFor_earlySupporterOf M F) S.C _ s _ (H u) u (hHeld u hu)
      (by rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]; exact (hHs u hu).2.2.2.2)
  have hSlot : ∀ vote ∈ M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1 - 1),
      vote.slot = s + 1 - 1 := by
    rw [hti]
    exact (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E kc v s
  have h := (GoldilocksCorrectness.Record.Proofs.Routines.update_confirmation_saves F) Hs
    (Nat.le_add_left 1 s) hRoots₂ hSup hSlot hVoters hUpdate
  rw [Nat.add_sub_cancel] at h
  rw [hSv]
  exact h

/-! ## Two honest-held blocks -/

/-- **Lemma 89a in the time form.** Under unforgeability, roots naming blocks, permanent
corruption and fewer than a third of the validators in the adversary set up to `tEnd`: when `v` is
honest at `t ≤ tEnd` and holds `D` before `t`, `p` is honest at `t' ≤ tEnd` and holds `B` before
`t'`, and `B`'s chain-state height is greater than the finalization height of `D`'s chain state,
then the finalized block of `D`'s chain state is `B` or an ancestor of `B`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `v`, `p`: the two holders; `D`, `B`: the two blocks.

Roots name blocks until `tR`, at least `max t t'`: Lemma 89a at the steps before `t` and before
`t'`.

Read aloud: Lemma 89a in the time form: the finalized block of a held block's chain state is an
ancestor of, or equal to, every honest-held block whose chain-state height is greater than its
finalization height. -/
theorem finalized_ancestorEq_of_held (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ}
      (hRoots : RootsNameBlocksUntil M A x tR)
    (tEnd t t' : ℕ) (v p : V) (D B : Block V)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hv : v ∉ A.corruptedAtTime x t) (hp : p ∉ A.corruptedAtTime x t')
    (hD : D ∈ (x.stateBefore t v).tree) (hB : B ∈ (x.stateBefore t' p).tree)
    (hlt : (M.chainStateOf S.C D).h_F < (M.chainStateOf S.C B).h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    (M.chainStateOf S.C D).F.AncestorEq B := by
  have hti := (time_stepBefore_le M) x R E t
  have htj := (time_stepBefore_le M) x R E t'
  have hT : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (x.stepBefore t)) (x.time (x.stepBefore t'))) :=
    hThird.mono (max_le (hti.trans (by exact_mod_cast ht)) (htj.trans (by exact_mod_cast ht')))
  have hv' : v ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R E hv (by exact_mod_cast hti)
  have hp' : p ∉ A.corrupted (x.stepBefore t') :=
    (not_mem_corrupted_of_le_time M) x R E hp (by exact_mod_cast htj)
  exact (lem68_honest_past_finalized M F Fx) S A x R E hRoots (x.stepBefore t) (x.stepBefore t') v p D B
    hT hv' hp' hD hB hlt (le_trans (max_le_max hti htj) (by exact_mod_cast htR))

/-- **Two justification certificates at one height, on the chains of two honest-held blocks, name
one block, when both blocks are held** (Lemma 76 and roots naming blocks). Under unforgeability,
roots naming blocks, permanent corruption and fewer than a third of the validators in the adversary
set up to `tEnd`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tEnd`, `t`, `t'`: the times;
  `p`, `w`: the two holders; `B₁`, `B₂`: the blocks carrying the certificates; `h`: the height;
  `T`, `T'`: the justified blocks.

Roots name blocks until `tR`, at least `max t t'`: the proof compares `T`, held by `p` before
`t`, with `T'`, held by `w` before `t'`.

Read aloud: two justification certificates at one height on the chains of two honest-held blocks
name one block. -/
theorem eq_of_cert_same_height (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ}
      (hRoots : RootsNameBlocksUntil M A x tR)
    (tEnd t t' : ℕ) (p w : V) (B₁ B₂ T T' : Block V) (h : Height)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tEnd) (ht : t ≤ tEnd)
      (ht' : t' ≤ tEnd)
    (hp : p ∉ A.corruptedAtTime x t) (hw : w ∉ A.corruptedAtTime x t')
    (hB₁ : B₁ ∈ (x.stateBefore t p).tree) (hB₂ : B₂ ∈ (x.stateBefore t' w).tree)
    (hJ : JustificationCertOn M B₁ h T)
    (hJ' : JustificationCertOn M B₂ h T')
    (hT : T ∈ (x.stateBefore t p).tree) (hT' : T' ∈ (x.stateBefore t' w).tree)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max t t' ≤ tR) :
    T = T' := by
  have hti := (time_stepBefore_le M) x R E t
  have htj := (time_stepBefore_le M) x R E t'
  have hA : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time (x.stepBefore t)) (x.time (x.stepBefore t'))) :=
    hThird.mono (max_le (hti.trans (by exact_mod_cast ht)) (htj.trans (by exact_mod_cast ht')))
  have hp' : p ∉ A.corrupted (x.stepBefore t) :=
    (not_mem_corrupted_of_le_time M) x R E hp (by exact_mod_cast hti)
  have hw' : w ∉ A.corrupted (x.stepBefore t') :=
    (not_mem_corrupted_of_le_time M) x R E hw (by exact_mod_cast htj)
  have hroot := (lem76_honest_one_justification M F Fx) S A x R E (x.stepBefore t) (x.stepBefore t') p w
    hA B₁ B₂ hB₁ hB₂ h T T' hJ hJ'
  exact hRoots T T' ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t) (v := p) hp' (le_trans hti (by exact_mod_cast (le_trans (le_max_left _ _) htR : t ≤ tR))) hT)
    ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := x.stepBefore t') (v := w) hw' (le_trans htj (by exact_mod_cast (le_trans (le_max_right _ _) htR : t' ≤ tR))) hT') hroot

end GoldilocksCorrectness.Record.Proofs.Executions

