module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.VoteDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ForkChoiceStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# What an honest voter holds and serves at its vote

Execution-level facts about an honest validator's Goldfish vote, read by the helpers that
take a voter as a holder of the sync fact (`Record/Restated/Statements/AbstractTrace/TraceDefs.lean`,
`SyncedWithinBy`):

- `tick_vote_fork_choice`: the vote a tick sends at the vote time of a slot is for the end of the
  Goldfish fork choice on the voter's state before the tick (moved here from
  `PeriodInductionCompat.lean`, unchanged);
- `vote_head_compatible_finalized_of_exec`: that block is the voter's finalized block before the vote
  time or a descendant of it (moved here from `SelectionKit.lean`, unchanged), and
  `vote_head_compatible_of_held`, the same for a named block of the voter's tree the vote names;
- `window_of_tickInput_awakeSince`: a validator whose tick reads a state awake since a time before
  the duty window's start of a slot is active through the one-delay windows that start at least
  three delays before that slot's vote time.

The page sits low in the import order so that the helpers of Lemma 12's family can read it.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor HeadOf AnchorAt)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **The vote a tick sends is the end of the Goldfish fork choice, on the state before the
tick.** For a Goldfish vote `w` put on the wire at its tick at the vote time of slot `s'`: the vote
is `w`'s slot-`s'` vote for a block `H_u` that `w` holds before the tick, and `H_u` is the end of
the walk of `w`'s Goldfish vote of slot `s'` on `w`'s node state before the tick (`HeadOf`), started
at the anchor `AnchorAt` over `w`'s frame with some set `E` of lock entries. Lemma 14 over the
record (`lem14_tick_vote_walk`, the field `tick_vote_head` of `F.tk3`), read as the proof of
`holder_vote_extends_B_orTwoPast` reads it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `w`: the voter;
  `vote`: the vote.

The landed statement names some revoked AC state `A'` and some tree `vbt`; the twin names the lock
entries `E` the anchor reads and the record's voter tree, through `HeadOf`.

Read aloud: the vote a tick sends at the vote time is for the block the Goldfish fork choice ends at
on the voter's state before the tick. -/
theorem tick_vote_fork_choice (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s' : ℕ) (w : V) (vote : GoldfishVote V)
    (hsend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C s') ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ (E : Finset M.LE) (H_u : Block V),
      H_u ∈ (x.tickInput w (M.voteTime S.C s')).tree ∧ vote = GoldfishVote.mk w s' H_u.root ∧
      HeadOf M S.C (x.tickInput w (M.voteTime S.C s'))
        (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C s'))) E
          ((M.voteTime S.C s' : ℕ) : Int))
        ((M.voteTime S.C s' : ℕ) : Int) s' H_u := by
  obtain ⟨i, hl, hm⟩ := hsend
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hΔ := one_le_Δ S
  have hv₃ : M.voteTime S.C s' = M.slotStart S.C s' + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hss : M.slotStart S.C (s' + 1) = M.slotStart S.C s' + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hslot : S.C.slot ((M.voteTime S.C s' : ℕ) : Int) = s' := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have hwi : w ∉ A.corrupted i :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active i w _ hl).1
  have hTIi : x.tickInput w (M.voteTime S.C s') = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M x E) hl]
  obtain ⟨-, n', sent, hrun, hvote, -, -⟩ := (tick_send_step_outcome_per_step M F R E) hl hm
  -- the tick's input state satisfies the node invariant (Lemma 11 at the tick's step)
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C s')) := by
    rw [hTIi]
    exact ((lem11_node_invariant M F S A x R E i w) hwi).1
  -- Lemma 14 over the record (T5, the field `tick_vote_head` of `F.tk3`): the vote is `w`'s, of slot
  -- `s'`, for the end `H_u` of the walk through the viable part of `w`'s voter tree from the anchor
  -- over `w`'s frame with the lock entries the tick left (`HeadOf`); the node was awake for the slot,
  -- so the tick ran from `w`'s state at step `i`
  obtain ⟨-, hvi, hvs, -, hAwT, H_u, hHead, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInvT hvote
  have hnv : (x.tickInput w (M.voteTime S.C s')).v = w :=
    (by rw [hTIi]; exact ((lem11_node_invariant M F S A x R E i w) hwi).2.1)
  rw [hnv] at hvi
  rw [hslot] at hvs
  rw [hslot] at hHead
  have hInvN : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C s')) := hInvT
  have hvote' : vote = GoldfishVote.mk w s' H_u.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable tree
  have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C s'))).tree,
      D ∈ (x.tickInput w (M.voteTime S.C s')).tree :=
    fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
  obtain ⟨votes, support_votes, hCV, hWalk⟩ := hHead
  have hHT : H_u ∈ (x.tickInput w (M.voteTime S.C s')).tree := by
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C s'))) n'.lockEntries
          ((M.voteTime S.C s' : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInvN]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvN
        · exact F.nd.nodeInv_finalized_mem_tree hInvN
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _
        H_u).1 h1).1
  exact ⟨n'.lockEntries, H_u, hHT, hvote', votes, support_votes, hCV, hWalk⟩


variable {S : Setup V} {A : Activity V}

/-- The head of an honest validator's Goldfish vote of the slot `s'`, put on the wire at its tick at
the vote time of `s'`, is a block of its tree before that time, whose root the vote names, and which
is its finalized block before that time or a descendant of it.

Why: the tick walks from the anchor over the node's frame (`tick_vote_fork_choice`), which is the
frame's fgroot or a block of its viable tree, and every walk from such a start ends at a descendant
of the finalized block (`vote_head_descends_of_F`), given the node invariant and that the finalized
block is the justified block or an ancestor of it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `x`: the setup, the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the
  trace is wake-shaped; `s'`: the slot; `u`: the voter; `vote`: the vote.

Read aloud: an honest validator votes for a block its finalized block does not prune. -/
theorem vote_head_compatible_finalized_of_exec (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s' : ℕ) (u : V) (vote : GoldfishVote V)
    -- `u` put `vote` on the wire at its tick at the vote time of `s'`
    (hsend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree, vote = GoldfishVote.mk u s' H_u.root ∧
      (x.tickInput u (M.voteTime S.C s')).finalized.AncestorEq H_u := by
  -- the tick's step `i`, by an active validator, is the step whose state the tick reads
  obtain ⟨i, hl, -⟩ := id hsend
  have hti : x.tickInput u (M.voteTime S.C s') = x.st i u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hv : u ∉ A.corrupted i :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active i u _ hl).1
  obtain ⟨Eb, H_u, hHT, hveq, votes, sv, -, hWalk⟩ :=
    (tick_vote_fork_choice M F U) R E s' u vote hsend
  rw [hti] at hHT hWalk ⊢
  exact ⟨H_u, hHT, hveq, (GoldilocksCorrectness.Record.Proofs.Routines.vote_head_descends_of_F M F)
    S.C S.P S.X _ ((lem11_node_invariant M F) S A x R E i u hv).1
    ((F_ancestorEq_J_of_exec M F) S A x R E i u)
    _ (GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M _ Eb _) _ _ votes sv _ H_u
    hWalk.1⟩

/-- The head of an honest validator's Goldfish vote of the slot `s'`, put on the wire at its tick at
the vote time of `s'`, when the vote names the root of a block `H` of the voter's tree before that
time, is compatible with the voter's finalized block before that time.

Why: the vote's head is the root of a block of the tree that is the finalized block or a descendant
of it (`vote_head_compatible_finalized_of_exec`), and no two blocks of the tree share a root (the
node invariant), so that block is `H`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `s'`: the slot; `u`: the voter; `H`: the block.

Read aloud: the block an honest validator votes for is one its finalized block does not prune. -/
theorem vote_head_compatible_of_held (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s' : ℕ) (u : V) (H : Block V)
    -- `u` put its vote for `H`'s root on the wire at its tick at the vote time of `s'`
    (hsend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' H.root)⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- `H` is a block of `u`'s tree before that time
    (hH : H ∈ (x.tickInput u (M.voteTime S.C s')).tree) :
    (x.tickInput u (M.voteTime S.C s')).finalized.compatible H = true := by
  obtain ⟨H_u, hHT, hveq, hanc⟩ := (vote_head_compatible_finalized_of_exec M F U) x R E s' u _ hsend
  have hroot : H.root = H_u.root := by
    have h := congrArg GoldfishVote.head hveq
    simpa using h
  obtain ⟨i, hl, -⟩ := hsend
  have hti : x.tickInput u (M.voteTime S.C s') = x.st i u := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hv : u ∉ A.corrupted i :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active i u _ hl).1
  rw [hti] at hH hHT hanc ⊢
  have hHH : H = H_u := (F.nd.nodeInv_rootsNameBlocksIn
    ((lem11_node_invariant M F) S A x R E i u hv).1) H hH H_u hHT hroot
  subst hHH
  exact (compatible_iff _ _).2 (Or.inl hanc)

/-! Their callers hold longer windows,
most of them from a duty window's start; the lemmas of this section open and build those windows
. -/

/-- The times of slot `s`, written from its start: the vote time one delay after it, the support
cutoff two, the view freeze three, the next slot's start four; the duty window's start `4Δk − Δ`
before it, or `0`; and `8Δ ≤ 4Δk`, `1 ≤ Δ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `s`: the slot.

Read aloud: the times of a slot, one delay apart, and its duty window's start. -/
theorem slot_times (U : UniformSchedule M.toSlotLayout) (S : Setup V) (s : ℕ) :
    M.voteTime S.C s = M.slotStart S.C s + Δ S ∧
    M.supportCutoff S.C s = M.slotStart S.C s + 2 * Δ S ∧
    M.viewFreeze S.C s = M.slotStart S.C s + 3 * Δ S ∧
    M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S ∧
    (M.dutyWindowStart S.C s + 4 * Δ S * S.C.k = M.slotStart S.C s + Δ S ∨
      (M.dutyWindowStart S.C s = 0 ∧ M.slotStart S.C s + Δ S < 4 * Δ S * S.C.k)) ∧
    8 * Δ S ≤ 4 * Δ S * S.C.k ∧ 1 ≤ Δ S := by
  have hv := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hc := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have hf := (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S s
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s
  have hs1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1)
  have hd := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S s
  have hk : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ S.C.k_ge_two
  have hΔ := one_le_Δ S
  rw [Nat.mul_add, Nat.mul_one] at hs1
  rw [← hss] at hd
  exact ⟨hv, by omega, hf, by omega, hd, by omega, hΔ⟩

omit F in
/-- A window from `a` through `e` gives the reader's window of length `c` ending at `b`, when it
starts at or before `b − c` and ends at or after `b`.

The variables:
- `A`: the activity; `v`: the validator; `a`, `e`: the ends of the window held; `b`: the end of
  the window built; `c`: its length.

Read aloud: a validator active through a longer window is active through every window inside it. -/
theorem activeThroughout_sub_of_window {Msg N : Type} {x : Trace V Msg N} {v : V} {a b c e : ℕ}
    (h : v ∈ A.activeThroughout x a e)
    (hcb : c ≤ b) (hab : a + c ≤ b) (hbe : b ≤ e) :
    v ∈ A.activeThroughout x (b - c) b := by
  refine Activity.mem_activeThroughout_of_le ?_ (by exact_mod_cast hbe) h
  have hab' : (a : ℝ) + c ≤ b := by exact_mod_cast hab
  linarith

omit F in
/-- The reader's window of length `c` ending at `b` gives the one of length `c'` ending at `b'`,
when the second is inside the first.

The variables:
- `A`: the activity; `v`: the validator; `b`, `c`: the end and the length of the window held;
  `b'`, `c'`: those of the window built.

Read aloud: a validator active through a window is active through every window inside it. -/
theorem activeThroughout_sub_of_sub {Msg N : Type} {x : Trace V Msg N} {v : V} {b c b' c' : ℕ}
    (h : v ∈ A.activeThroughout x (b - c) b)
    (hcb : c ≤ b) (hcb' : c' ≤ b') (hle : b - c ≤ b' - c') (hbb : b' ≤ b) :
    v ∈ A.activeThroughout x (b' - c') b' := by
  refine Activity.mem_activeThroughout_of_le ?_ (by exact_mod_cast hbb) h
  rw [← Nat.cast_sub hcb, ← Nat.cast_sub hcb']
  exact_mod_cast hle

omit F in
/-- The reader's window of length `c` ending at `b` gives the window from every later start `t₀`
through every earlier end `e ≤ b`, in the natural-number spelling.

The variables:
- `A`: the activity; `v`: the validator; `b`, `c`: the end and the length of the window held;
  `t₀`, `e`: the start and the end of the window built.

Read aloud: a validator active through a window is active through every window inside it. -/
theorem activeThroughout_of_sub {Msg N : Type} {x : Trace V Msg N} {v : V} {b c t₀ e : ℕ}
    (h : v ∈ A.activeThroughout x (b - c) b)
    (hcb : c ≤ b) (h0 : b ≤ t₀ + c) (he : e ≤ b) :
    v ∈ A.activeThroughout x t₀ e := by
  refine Activity.mem_activeThroughout_of_le ?_ (by exact_mod_cast he) h
  have h0' : (b : ℝ) ≤ t₀ + c := by exact_mod_cast h0
  linarith

/-- A validator active from the duty window's start of slot `s` through `e` is active through the
window of length `max (Δ S) Δs` ending at every `b ≤ e` with the vote time of `s` at most
`b + 3 * Δ S` and `max (Δ S) Δs ≤ b`, under `max (Δ S) Δs + 3 * Δ S + ΔClockAhead + ΔClockBehind <
4 * Δ S * S.C.k` with `0 ≤ ΔClockAhead + ΔClockBehind` (the interval of real times a tick to a clock
value may take is not empty).

Why: the duty window starts `4Δk − Δ` before slot `s` starts, so `4Δk` before its vote time, and
`max (Δ S) Δs + 3 * Δ S ≤ 4Δk`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `S`: the setup; `A`: the
  activity; `Δs`: the sync delay; `hΔs`: its bound; `s`: the slot; `v`: the validator; `b`: the
  end of the window built; `e`: the end of the window held.

Read aloud: a duty window holds every one-delay window ending at most three delays before the
vote time. -/
theorem activeThroughout_of_dutyWindow {Msg N : Type} {x : Trace V Msg N} (U : UniformSchedule M.toSlotLayout) (S : Setup V)
    {Δs : ℕ} {ΔClockAhead ΔClockBehind : ℝ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- the two clock bounds leave a nonempty interval around every clock value
    (hskew : 0 ≤ ΔClockAhead + ΔClockBehind) {s b e : ℕ} {v : V}
    (h : v ∈ A.activeThroughout x (M.dutyWindowStart S.C s) e)
    (hb : M.voteTime S.C s ≤ b + 3 * Δ S) (hcb : max (Δ S) Δs ≤ b) (hbe : b ≤ e) :
    v ∈ A.activeThroughout x (b - (max (Δ S) Δs)) b := by
  obtain ⟨hv, -, -, -, hd, hk, hΔ⟩ := (slot_times M F U) S s
  have hΔs' : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h' : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'
  have hmx1 := le_max_left (Δ S) Δs
  have hmx2 := le_max_right (Δ S) Δs
  refine Activity.mem_activeThroughout_of_le ?_ (by exact_mod_cast hbe) h
  rw [← Nat.cast_sub hcb]
  have hle : M.dutyWindowStart S.C s ≤ b - max (Δ S) Δs := by
    rcases max_choice (Δ S) Δs with hm | hm <;> rcases hd with hd | ⟨hd, -⟩ <;> omega
  exact_mod_cast hle

/-- A validator that ticks to the clock value `t` at the step `k` from a state awake since a time `τ`
at most the protocol's duty window start of slot `s'` is active through the window starting
`max (Δ S) Δs` before every `b` with `max (Δ S) Δs ≤ b` and the vote time of `s'` at most `b + 3 * Δ S`,
and ending at every `e` more than `ΔClockAhead` before `t`, under
`max (Δ S) Δs + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k`.

Why: the stored wake time is the initial one, and `u` was awake after every step up to its tick, or
`u` ticked to `τ` at a step `k₁` before `k` after its last restart and stayed awake from `k₁` to `k`
(`awake_of_tickInput_awakeSince_of_tick`). Every step of the window is before `k` (the tick is at a real
time at least `t − ΔClockAhead`), and, in the second case, from `k₁` on (the tick to `τ` is at a real
time at most `τ + ΔClockBehind`, more than `ΔClockBehind` before the window by `hb` and `hΔs`); honest at
every step up to `k` by the permanence of corruption.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `x`, `R`, `E`: the execution,
  its run facts and its delivery promise; `hΔs`: the sync delay's bound; `s'`: the slot; `t`: the
  tick's clock value; `k`: the tick's step; `b`: the time the window starts `max (Δ S) Δs` before; `e`:
  its end; `u`: the validator; `τ`: the time since which its state is awake.

Read aloud: a validator whose tick reads a state awake since before a duty window's start is active through
every one-delay window that starts at least three delays before that slot's vote time and ends by
the tick. -/
theorem window_of_tickInput_awakeSince (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {s' t b e k : ℕ} {u : V} {τ : Time}
    -- `u` ticks to `t` at the step `k`
    (hk : x.lbl k = Event.tick u t)
    -- the state that tick reads has been awake since `τ`, at most the duty window's start
    (hτ : (x.tickInput u t).awakeSince = some τ) (hτle : τ ≤ duty_window_start S.C s')
    -- the window starts at least three delays before the vote time of `s'`, and ends more than
    -- `ΔClockAhead` before `t`
    (hb : M.voteTime S.C s' ≤ b + 3 * Δ S) (hcb : max (Δ S) Δs ≤ b) (he : (e : ℝ) + ΔClockAhead < t) :
    u ∈ A.activeThroughout x (b - (max (Δ S) Δs)) e := by
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hd : ((duty_window_start S.C s' : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (s' : ℝ) + (Δ S : ℝ) - 4 * (Δ S : ℝ) * (S.C.k : ℝ) := by
    have h := GoldilocksCorrectness.Proofs.Routines.Δ_cast S
    rw [GoldilocksCorrectness.Proofs.Routines.duty_window_start_eq,
      GoldilocksCorrectness.Proofs.Routines.t_eq_mul, ← h]
    push_cast
    ring
  have hvt := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s'
  have hss := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S s'
  have hmc : ((max (Δ S) Δs : ℕ) : ℝ) = max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := Nat.cast_max _ _
  have hsub : ((b - max (Δ S) Δs : ℕ) : ℝ) = (b : ℝ) - ((max (Δ S) Δs : ℕ) : ℝ) := Nat.cast_sub hcb
  have hbR : ((M.voteTime S.C s' : ℕ) : ℝ) ≤ (b : ℝ) + 3 * Δ S := by exact_mod_cast hb
  have hvR : ((M.voteTime S.C s' : ℕ) : ℝ) = 4 * Δ S * s' + Δ S := by rw [hvt, hss]; push_cast; ring
  -- the window starts more than `ΔClockBehind` after the duty window's start
  have hstart : ((duty_window_start S.C s' : ℤ) : ℝ) + ΔClockBehind < ((b - max (Δ S) Δs : ℕ) : ℝ) := by
    rw [hsub, hd]; linarith [hmc]
  have hkt := (E.tick_active k u t hk).2.1
  have hvk : u ∉ A.corrupted k := E.not_mem_corrupted_of_tick hk
  have hstep : x.tickStep u t = k := (tickStep_eq_of_lbl M) x E hk
  have hcases := (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨k, hk⟩ hτ
  rw [hstep] at hcases
  refine Activity.mem_activeThroughout_of_forall fun i h1 h2 => ?_
  have h2' : ((b - max (Δ S) Δs : ℕ) : ℝ) ≤ x.time (i + 1) := by
    first | exact h2 | (rw [hsub]; exact h2)
  have hik : i < k := (lt_of_time_lt M) x R (by linarith)
  clear h2
  refine Activity.mem_active.2 ⟨?_, fun hc => hvk (E.corrupted_mono i k hik.le hc)⟩
  rcases hcases with ⟨-, hall⟩ | ⟨k₁, τ', -, hl₁, hτ', hawk⟩
  · exact hall i hik.le
  · refine hawk i ?_ hik.le
    have hk₁t := (E.tick_active k₁ u τ' hl₁).2.2
    have hτ'R : (τ' : ℝ) ≤ ((duty_window_start S.C s' : ℤ) : ℝ) := by
      have : ((τ' : ℤ) : ℝ) ≤ ((duty_window_start S.C s' : ℤ) : ℝ) := by exact_mod_cast (hτ' ▸ hτle)
      exact_mod_cast this
    by_contra hc
    have := R.time_mono (show i + 1 ≤ k₁ by omega)
    linarith

end GoldilocksCorrectness.Record.Proofs.Executions
