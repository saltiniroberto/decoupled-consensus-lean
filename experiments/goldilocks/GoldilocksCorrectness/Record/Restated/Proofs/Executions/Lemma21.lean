module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma21, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma21.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 21, the next slot's honest Goldfish vote
extends an eligible block. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq viewFreeze_cast viewFreeze_eq voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor CountedVotesAt EarlySupporterOf
  VoterTree VoterTreeAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A validator of the window `A.activeThroughoutToTick x (duty_window_start S.C (s + 1))
(M.supportCutoff S.C (s + 1))` ticks to the support cutoff of slot `s + 1` at a step `kR` and is
active after every step from the first one whose time is that cutoff minus `max (Δ S) Δs` up to
`kR`: under `hΔs` the protocol's duty window start, `4 Δ k − Δ` before the slot's start, is more than
`ΔClockBehind` before that time (`tick_window_of_activeThroughoutToTick_int`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `R`: the run's facts; `E`: the environment's facts; `hΔs`: the bound on the sync
  delay; `s`: the slot; `v`: the validator.

Read aloud: a validator active from the duty window's start of slot `s + 1` up to its tick to that
slot's support cutoff is active from one delay or one sync delay before the cutoff up to that tick. -/
theorem tick_window_of_dutyWindow (U : UniformSchedule M.toSlotLayout) (S : Setup V) {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {s : ℕ} {v : V}
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    ∃ kR : ℕ, x.lbl kR = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      ∀ i : ℕ, M.supportCutoff S.C (s + 1) - max (Δ S) Δs ≤ x.time i → i ≤ kR → v ∈ A.active i := by
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  -- the duty window's start is `4 Δ S k − Δ S` before the slot's start: more than both clock bounds
  -- before the cutoff less `max (Δ S) Δs`, by `hΔs` ('s bound; `behind_nonneg`, `ahead_nonneg`)
  have hmc : ((max (Δ S) Δs : ℕ) : ℝ) = max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hmx : ((max (Δ S) Δs : ℕ) : ℝ) + 3 * Δ S + ΔClockBehind < 4 * Δ S * S.C.k := by
    linarith [E.ahead_nonneg, hmc]
  have hd := duty_window_start_real S (s + 1)
  have hc : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * (s + 1 : ℕ) + 2 * Δ S := by
    rw [hsc, hvt, hss]
    push_cast
    ring
  have hΔ0 : (0 : ℝ) ≤ Δ S := by positivity
  obtain ⟨kR, hk1, hk2⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ)) (by
      rw [hc, hd]
      push_cast
      linarith)
  exact ⟨kR, hk1, fun i hi hik => hk2 i hi hik⟩

/-- **Lemma 21b's reads of `v` from the duty window's reader.** A validator `v` of
`A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))`, under `hΔs`,
`hSkew`, the sync delay and one delay fitting before the view freeze of slot `s` (`hfr`), and a window
start `tStartW` more than both clock bounds before the view freeze of slot `s` less `max (3 * Δ S) Δs`:
the duty window's start, as an integer, is more than both clock bounds before the support cutoff of slot
`s + 1` less `max (6 * Δ S) Δs` (Lemma 21b's `htStart`), and `v` is active for the sync delay after the
view freeze of slot `s` less `max (Δ S) Δs`.

Why: the duty window's start is `4 * Δ S * k − Δ S` before the start of slot `s + 1`, and `hΔs` makes
`k` at least `2` and that start early enough, at every slot. `hfr` keeps the natural
subtraction `M.viewFreeze S.C s - max (Δ S) Δs` uncut, so the holder window ends by the view freeze of
slot `s`, more than `ΔClockAhead` before `v`'s tick to the support cutoff of slot `s + 1`, and starts
after the duty window's start (`mem_activeThroughout_of_mem_activeThroughoutToTick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `R`: the run's facts; `E`: the environment's facts; `hSkew`, `hΔs`: the bounds;
  `s`: the slot; `hfr`: the sync delay and one delay fit before the view freeze of slot `s`;
  `tStartW`: the start of the voter's window; `v`: the validator.

Read aloud: a validator active from the duty window's start of slot `s + 1` up to its tick to that
slot's support cutoff gives the window start and the holder window Lemma 21b reads, when the sync
delay and one delay fit before the view freeze of slot `s`. -/
theorem lem21b_reads_of_dutyWindow (U : UniformSchedule M.toSlotLayout) (S : Setup V) {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver}
    {ΔClockAhead ΔClockBehind : ℝ} (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {s : ℕ} {tStartW : ℤ} {v : V}
    (hfr : max (Δ S) Δs ≤ M.viewFreeze S.C s)
    (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1))) :
    ((duty_window_start S.C (s + 1) : ℤ) : ℝ) + ΔClockAhead + ΔClockBehind <
        ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ∧
      v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs) := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
  have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hvf := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hsum : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
    rw [hsc, hvt, hvf, hss1, hss0]; ring
  have hfrN : M.viewFreeze S.C s = 4 * Δ S * s + 3 * Δ S := by rw [hvf, hss0]
  have h1a := le_max_left (Δ S) Δs
  have h1b := le_max_right (Δ S) Δs
  have h6a := le_max_left (6 * Δ S) Δs
  have h6b := le_max_right (6 * Δ S) Δs
  -- `hfr` and the view freeze's `3 * Δ S` keep the support cutoff of slot `s + 1` past `max (6 * Δ S) Δs`
  have hm6le : max (6 * Δ S) Δs ≤ M.supportCutoff S.C (s + 1) := by
    rcases max_cases (6 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hmc : ((max (Δ S) Δs : ℕ) : ℝ) = max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hmΔ : ((Δ S : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_left _ _
  have hmΔs : (Δs : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_right _ _
  have hc6 : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) =
      (M.supportCutoff S.C (s + 1) : ℝ) - ((max (6 * Δ S) Δs : ℕ) : ℝ) := Nat.cast_sub hm6le
  have hc1 : ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) =
      (M.viewFreeze S.C s : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ) := Nat.cast_sub hfr
  have hscR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * Δ S * (s : ℝ) + 6 * Δ S := by
    rw [hsum, hfrN]; push_cast; ring
  have hfrR : ((M.viewFreeze S.C s : ℕ) : ℝ) = 4 * Δ S * (s : ℝ) + 3 * Δ S := by
    rw [hfrN]; push_cast; ring
  have hk2 : (2 : ℝ) ≤ S.C.k := by
    have h1 : (1 : ℝ) < S.C.k := by
      by_contra hc
      push_neg at hc
      have : (4 * Δ S * S.C.k : ℝ) ≤ 4 * Δ S * 1 := by
        apply mul_le_mul_of_nonneg_left hc; positivity
      linarith
    have h1' : 1 < S.C.k := by exact_mod_cast h1
    exact_mod_cast h1'
  have hk8 : (8 * Δ S : ℝ) ≤ 4 * Δ S * S.C.k := by
    have : (4 * Δ S * 2 : ℝ) ≤ 4 * Δ S * S.C.k := by
      apply mul_le_mul_of_nonneg_left hk2; positivity
    linarith
  have hd := duty_window_start_real S (s + 1)
  refine ⟨?_, ?_⟩
  · -- the duty window's start, as an integer, is `4 Δ S k − Δ S` before the start of slot `s + 1`
    rw [hc6, hscR, hd]
    rcases max_cases (6 * Δ S) Δs with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]; push_cast; nlinarith
    · rw [hm]; push_cast; nlinarith
  · have h := (mem_activeThroughout_of_mem_activeThroughoutToTick M F) R E hv
      (a' := M.viewFreeze S.C s - max (Δ S) Δs) (e := M.viewFreeze S.C s - max (Δ S) Δs + Δs)
      (by rw [hc1, hfrR, hmc, hd]; push_cast; linarith)
      (by
        have : M.viewFreeze S.C s - max (Δ S) Δs + Δs ≤ M.viewFreeze S.C s := by omega
        have : ((M.viewFreeze S.C s - max (Δ S) Δs + Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
          exact_mod_cast this
        rw [hsum]; push_cast at this ⊢; linarith)
    rw [Nat.cast_add] at h
    exact h

/-- **Lemma 21, the held form.** Lemma 21's conclusion, naming the block: `vote` is `w`'s
slot-`(s + 1)` vote for a block `H_w` of `w`'s tree at its tick to the vote time of slot `s + 1`, and
`H_w` is `B` or a descendant of `B`.

Why: Lemma 21's proof, keeping the walk's end. Lemma 14 gives the vote's validator and slot (the
validator of the tick's input state is `w`, Lemma 11) and the walk; its end is a block of the
viable tree of `w`'s voter tree or the walk's start, the anchor, which is in `w`'s tree
(`get_anchor_mem_T`); Lemma 64 puts it on `B`'s chain.

Read at the validators' own ticks (T-RC8-2, the shape Lemma 42 takes): `v` from `tStart` up to its
tick to the support cutoff of slot `s + 1`, `w` from `tStartW` up to its tick to the view freeze of
slot `s`, the holders `v` and `w` for the sync delay after the sync fact's read times,
the roots until the latest real time of `w`'s tick to the view freeze of slot `s` (T-R51's form).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the network is
  synchronous; `s`: the slot of the eligibility;
- `Sup`: the early supporters; `B`: the eligible block; `v`: the validator finding it eligible;
  `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote; `tStart`, `tStartW`: the starts of `v`'s
  and `w`'s windows.

Read aloud: under Lemma 21's hypotheses read at the validators' ticks, `w`'s vote is its
slot-`(s + 1)` vote for a block `w` holds at its tick to that vote time that is `B` or a descendant of
`B`. -/
theorem lem21b_goldfish_vote_extends_eligible_block_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold, until the latest real time of `w`'s tick
    -- to the view freeze of slot `s`, the one receiver of a block (T-RC8-2, T-R42's form)
    (hRoots : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`'s window starts at `tStart`, more than both clock bounds before the support cutoff of slot `s + 1`
    -- less six delays or one sync delay, whichever is longer
    (tStart : ℤ) (htStart :
      (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ))
    -- `v` is active from `tStart` up to its tick to the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeThroughoutToTick x tStart (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- the holders: `v` active for the sync delay after the view freeze of slot `s` less one
    -- delay or one sync delay, whichever is longer; `w` for the sync delay after the support cutoff of
    -- slot `s + 1` less the same
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hSup : ∀ u ∈ Sup,
      EarlySupporterOf M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s B u)
    (hEligible :
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
        2 * Sup.card)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ B.AncestorEq W)
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ B.AncestorEq H_w := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  -- the times
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (s + 2) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_add]
    omega
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := hss2
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc : M.supportCutoff S.C s = M.voteTime S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have ht₂ : M.supportCutoff S.C (s + 1) = M.voteTime S.C (s + 1) + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
  have hfr : M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hfr' : M.supportCutoff S.C s + Δ S = M.viewFreeze S.C s := by omega
  have ht₂' : M.voteTime S.C (s + 1) + Δ S = M.supportCutoff S.C (s + 1) := ht₂.symm
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm6 : max (6 * Δ S) Δs ≥ 6 * Δ S := le_max_left _ _
  have hm6' : max (6 * Δ S) Δs ≥ Δs := le_max_right _ _
  have hm3 : max (3 * Δ S) Δs ≥ 3 * Δ S := le_max_left _ _
  have hm3' : max (3 * Δ S) Δs ≥ Δs := le_max_right _ _
  have hslot₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
      (by omega) (by omega)
  -- `v`'s tick `k_v` to the support cutoff of slot `s + 1`, active from the support cutoff of slot `s` less
  -- `ΔClockAhead`
  have hslR : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.supportCutoff S.C s : ℝ) := by
    exact_mod_cast (show M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs ≤ M.supportCutoff S.C s by omega)
  obtain ⟨k_v, hk_v, hwinv⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hv
    (t₀ := (M.supportCutoff S.C s : ℝ) - ΔClockAhead) (by linarith)
  have hk_vT := (E.tick_active k_v v _ hk_v).2.1
  have hcR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s : ℝ) + 4 * Δ S := by
    have : M.supportCutoff S.C (s + 1) = M.supportCutoff S.C s + 4 * Δ S := by omega
    rw [this]; push_cast; ring
  rw [hcR] at hk_vT
  -- `v`'s tick `kₑ` to the support cutoff of slot `s`
  obtain ⟨kₑ, hkₑ, -, -⟩ := E.tick_of_active (M.supportCutoff S.C s) (by omega) v fun j hj1 hj2 => by
    refine hwinv j hj1 ?_
    exact ((lt_of_time_lt M) x R (by linarith)).le
  -- `w`'s tick `k_f` to the view freeze of slot `s`
  have hslW : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.viewFreeze S.C s : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  obtain ⟨k_f, hk_f, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hw
    (t₀ := (M.viewFreeze S.C s : ℝ)) (by linarith)
  -- `w`'s run and walk: Lemma 14 over the record, from the input state of its tick to the vote time of
  -- slot `s + 1` (`w` is active at that step, Lemma 11)
  obtain ⟨i, hl, hm⟩ := hSend
  have hTI : x.tickInput w (M.voteTime S.C (s + 1)) = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  obtain ⟨hact, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  have hInv11 := (lem11_node_invariant M F S A x R E i w) (Activity.not_mem_corrupted_of_mem_active hact)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hTI]
    exact hInv11.1
  obtain ⟨-, hvi, hvs, -, hAwake, H_w, ⟨votes, support_votes, hCounted, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent
      vote hrun hInvT hvote
  rw [hslot₃] at hvs hAwake hCounted hWalk
  rw [Nat.add_sub_cancel] at hWalk
  -- the vote is `w`'s slot-`(s + 1)` vote for `H_w` (the validator of the tick's input state is `w`)
  rw [hTI, hInv11.2.1] at hvi
  have hvote' : vote = GoldfishVote.mk w (s + 1) H_w.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable tree
  have hHwT : H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
    have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree,
        D ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
      fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries
          ((M.voteTime S.C (s + 1) : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F),
          F.ndAdded.get_fc_root_eq hInvT]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvT
        · exact F.nd.nodeInv_finalized_mem_tree hInvT
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1
          h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _
        (s + 1) H_w).1 h1).1
  -- the spec's cutoffs are the reading points, cast; `w`'s voter's tree is the record's `VoterTree`,
  -- whose members are the blocks `VoterTreeAt` names
  have hCountedAt : CountedVotesAt M (x.tickInput w (M.voteTime S.C (s + 1)))
      ((M.viewFreeze S.C s : ℕ) : Int) (s + 1) votes support_votes := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
    exact hCounted
  have hvbtAt : ∀ B' : Block V,
      B' ∈ VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) ↔
        VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1))) ((M.viewFreeze S.C s : ℕ) : Int)
          (s + 1) B' := by
    intro B'
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
    simp only [VoterTree, Finset.mem_filter, Nat.add_sub_cancel]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  have hSupAt : ∀ u ∈ Sup, EarlySupporterAt M (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C s : ℕ) : Int) s B u := by
    intro u hu
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U)]
    exact hSup u hu
  have hF3' : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B →
      ∃ W ∈ VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1),
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          B.AncestorEq W := by
    intro hR
    obtain ⟨W, hW, hWv, hBW⟩ := hF3 hR
    refine ⟨W, ?_, hWv, hBW⟩
    simp only [VoterTree, Finset.mem_filter]
    exact ⟨hW.1, hW⟩
  -- Lemma 64 at the spec's times, with `t_e := c`, `t_f := freeze`, `t_w := t₃`, `t_v := t₂`; the anchor over
  -- the lock entries `n'` leaves (the lock clause of the vote time at the outcome `n'` of `w`'s tick)
  exact ⟨H_w, hHwT, hvote',
    (lem64_goldfish_vote_extends_eligible_block_at M F U) S A x R GST s (M.supportCutoff S.C s)
      (M.viewFreeze S.C s) (M.voteTime S.C (s + 1)) (M.supportCutoff S.C (s + 1))
      (M.supportCutoff S.C (s + 1)) Sup B v w n'.lockEntries votes support_votes
      (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1)) H_w
      (E.upTo _) hNet hSkew hRedeliver (Sy.upTo _)
      (by rw [hfr']; exact hRoots) hParent (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
      tStartW (by rw [hfr']; exact (lt_natSub_max_of_le (m := Δ S) (by omega) htStartW))
      (by
        have : ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C s : ℝ) := by
          exact_mod_cast (show M.viewFreeze S.C s - max (3 * Δ S) Δs ≤ M.slotStart S.C s by omega)
        linarith)
      (by rw [hfr']; exact hw)
      tStart (by rw [ht₂']; exact (lt_natSub_max_of_le (m := Δ S) (by omega) htStart))
      (by
        have : ((M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs : ℕ) : ℝ) ≤ (M.slotStart S.C s : ℝ) := by
          exact_mod_cast (show M.supportCutoff S.C (s + 1) - max (6 * Δ S) Δs ≤ M.slotStart S.C s by omega)
        linarith)
      (by rw [ht₂']; exact hv)
      (by rw [hfr']; exact hv₀) (by rw [ht₂']; exact hw₀)
      kₑ hkₑ k_f hk_f i hl k_v hk_v hSupAt hEligible hCountedAt hvbtAt hWalk hF2 hF3'
      (fun e he hlive => hLocks n' sent hrun hAwake e he hlive) (by omega)⟩

/-- Lemma 21, the next slot's honest vote extends a block an honest validator finds eligible (G2
over executions). Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/EligibleBlockVoteStatements.lean`.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 64, which the proof calls with `t_w :=
voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s fork choice.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the head of the Goldfish vote `w` sends at the vote time of slot `s + 1` is the root of
a block that is `B` or a descendant of `B`, when `B` is eligible at `v`'s update of slot `s`, the
finality-gadget conditions hold for `B` at `w`, and no live lock entry `w`'s tick leaves conflicts
with `B`. -/
theorem lem21_goldfish_vote_extends_eligible_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`, awake and honest from the duty window's start of slot `s + 1` up to its tick to that
    -- slot's support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `B` is eligible at `v`'s update of slot `s`: each member of `Sup` is an early supporter of
    -- `B`'s chain at `v`, and `v`'s late voters are fewer than twice `Sup`
    (hSup : ∀ u ∈ Sup,
      EarlySupporterOf M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s B u)
    (hEligible :
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
        2 * Sup.card)
    -- the finality-gadget conditions at `w`, on its state before `voteTime S (s + 1)`
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ B.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `B`
    (hLocks : ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ B.AncestorEq H_w := by
  obtain ⟨htStart, hv₀'⟩ := (lem21b_reads_of_dutyWindow M F U) S R E hSkew hΔs (le_of_add_le_right hGST) htStartW hv
  -- the roots until the latest real time of `w`'s tick to the view freeze of slot `s`
  have hRoots' : RootsNameBlocksUntil M A x ((M.viewFreeze S.C s : ℝ) + ΔClockBehind) := by
    have hB0 := E.behind_nonneg
    have hA0 := E.ahead_nonneg
    have hss1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
    have hss0 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
    have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
    have hsc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (s + 1)
    have hfr := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
    refine (RootsNameBlocksUntil.mono M) ?_ hRoots
    have : (M.supportCutoff S.C (s + 1) : ℝ) = (M.viewFreeze S.C s : ℝ) + 3 * Δ S := by
      have h : M.supportCutoff S.C (s + 1) = M.viewFreeze S.C s + 3 * Δ S := by
        rw [hsc, hvt, hfr, hss1, hss0]; ring
      rw [h]; push_cast; ring
    rw [this]
    have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast one_le_Δ S
    linarith
  -- Lemma 21, the held form
  obtain ⟨H_w, -, hvote', hB⟩ := (lem21b_goldfish_vote_extends_eligible_block_held M F U) S A x R GST s Sup B v w
    vote E hNet hSkew hRedeliver Sy hΔs hRoots' hParent hGST (duty_window_start S.C (s + 1)) htStart hv tStartW
    htStartW hw hv₀' hw₀ hSup hEligible hF2 hF3 hLocks hSend
  exact ⟨H_w, by rw [hvote'], hB⟩

end GoldilocksCorrectness.Record.Proofs.Executions

