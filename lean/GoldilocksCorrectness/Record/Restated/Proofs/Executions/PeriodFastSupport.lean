module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f

@[expose] public section

/-!
# PeriodFastSupport, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodFastSupport.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: a Goldfish vote an honest tick sent
is for a block held before the tick, and a fast block has an honest active supporter. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff
  expireLocks_keepsVotes fast_test_eq_ok_true_iff goldfish_fork_choice_eq wake_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (SupportVotes EarlyVotes)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Proofs.Routines
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff
  expireLocks_keepsVotes fast_test_eq_ok_true_iff goldfish_fork_choice_eq one_le_Δ wake_eq)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A Goldfish vote an honest tick sent is for a block held before the tick.** When the step
`k` ticks every awake validator at `t'` and puts on the wire `v`'s Goldfish vote `vote` for slot
`s`, then `t'` is the vote time of slot `s`, and `vote` is `v`'s vote for slot `s` whose head is
the root of a block `H_v` of the tree that tick reads.

Why: Lemma 14 (`lem14_tick_vote_walk`): the tick at `t'` sends a vote only at the vote time of the
slot of `t'`, for that slot, as the validator's, with the head the root of the block the fork
choice's walk ends at; that block is the anchor of the revoked state or a block of the voter
tree, both held. The proof of `holder_vote_extends_B_orTwoPast`, up to `hHT`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step of the tick; `t'`: its
  time; `v`: the voter; `s`: the slot of the vote; `vote`: the vote.

Read aloud: an honest tick's Goldfish vote is for a block the voter held before the tick. -/
theorem tick_vote_held_block (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k t' : ℕ} {v : V} {s : ℕ} {vote : GoldfishVote V}
    (hl : x.lbl k = Event.tick v t')
    (hm : (⟨v, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (k + 1) - x.sent k)
    (hs : vote.slot = s) :
    t' = M.voteTime S.C s ∧ ∃ H_v ∈ (x.tickInput v (M.voteTime S.C s)).tree,
      vote = GoldfishVote.mk v s H_v.root := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  obtain ⟨-, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F R E) hl hm
  have hTI_k : x.tickInput v t' = x.st k v := by
    show x.st (x.tickStep v t') v = x.st k v
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hvk : v ∉ A.corrupted k := E.not_mem_corrupted_of_tick hl
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t') := by
    rw [hTI_k]
    exact (lem11_node_invariant M F S A x R E k v hvk).1
  obtain ⟨ht'', hvi, hvs, -, -, H_u, ⟨votes, support_votes, -, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote
      hrun hInvT hvote
  have hslt : S.C.slot (t' : Int) = s := by rw [← hvs, hs]
  have hvt : t' = M.voteTime S.C s := by
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U) S s
    rw [hslt] at ht''
    rw [← ht''] at h1
    exact_mod_cast h1.symm
  subst hvt
  refine ⟨rfl, ?_⟩
  have hnv : (x.tickInput v (M.voteTime S.C s)).v = v := by
    rw [hTI_k]
    exact (lem11_node_invariant M F S A x R E k v hvk).2.1
  rw [hnv] at hvi
  rw [hslt] at hWalk
  have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput v (M.voteTime S.C s))).tree,
      D ∈ (x.tickInput v (M.voteTime S.C s)).tree :=
    fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
  refine ⟨H_u, ?_, ?_⟩
  · rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M
          (M.fg_to_ac (x.tickInput v (M.voteTime S.C s))) n'.lockEntries
          ((M.voteTime S.C s : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInvT]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvT
        · exact F.nd.nodeInv_finalized_mem_tree hInvT
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _
        H_u).1 h1).1
  · rw [← hvi, ← hs, ← hhead]

/-- **Kit fact, a step whose clock value is less than a later tick's comes no later than that tick.**
When `v` ticks to the clock value `t` at step `m`, and `v` is outside the adversary set after `j`
steps with its clock value there less than `t`, then `j ≤ m`.

Why: were `m < j`, the clock value after `m + 1` steps is `t` (`clockValue_succ_of_tick`) and an
honest validator's clock value never goes back up to step `j` (`clockValue_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `m`: the tick's step; `j`: the step; `v`: the
  validator; `t`: the tick's value.

Read aloud: while an honest validator's clock reads less than `t`, its tick to `t` is still to come. -/
theorem le_tick_of_clockValue_lt {A : Activity V} {x : Trace V (NamedObject V) M.N}
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {m j : ℕ} {v : V} {t : ℕ}
    -- step `m` is `v`'s tick to `t`
    (hm : x.lbl m = Event.tick v t)
    -- `v` is outside the adversary set after `j` steps
    (hv : v ∉ A.corrupted j)
    -- `v`'s clock value after `j` steps is less than `t`
    (hlt : x.clockValue j v < t) : j ≤ m := by
  by_contra h
  have h1 := E.clockValue_mono (show m + 1 ≤ j by omega) hv
  rw [x.clockValue_succ_of_tick hm] at h1
  omega

/-- **Kit fact, a vote stamped before a tick's value entered the pool by that tick.** When `u` ticks to
the clock value `t` at step `m`, is outside the adversary set after `K` steps, and its pool of slot `s`
after `K` steps holds `vote` stamped before `t`, then its pool of slot `s` already held `vote` after
some step `j ≤ m`.

Why: the vote entered the pool after some step `k + 1 ≤ K` and is stamped with `u`'s clock value
there (`voteStamp_entry_clock`, `clock_eq_clockValue`); that clock value is less than `t`, so
`k + 1 ≤ m` (`le_tick_of_clockValue_lt`, `u` honest after `k + 1` steps by `corrupted_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `K`: the step read; `m`: the
  tick's step; `u`: the validator; `t`: the tick's value; `s`: the slot; `vote`: the vote; `τ`: its
  stamp.

Read aloud: a vote an honest validator stamped before `t` was in its pool by its tick to `t`. -/
theorem vote_held_by_tick_of_stamp_lt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {K m : ℕ} {u : V} {t : ℕ} {s : Slot} {vote : GoldfishVote V} {τ : Stamp}
    -- step `m` is `u`'s tick to `t`
    (hm : x.lbl m = Event.tick u t)
    -- `u` is outside the adversary set after `K` steps
    (huK : u ∉ A.corrupted K)
    -- `u`'s pool of slot `s` after `K` steps holds `vote`, stamped `τ`, before `t`
    (hv : vote ∈ M.votesHeldSet (x.st K u) s) (hτ : (x.st K u).voteStamp vote = some τ)
    (hlt : τ < (((t : ℕ) : Int) : Stamp)) :
    ∃ j ≤ m, vote ∈ M.votesHeldSet (x.st j u) s := by
  obtain ⟨k, hk, -, hk1, hst⟩ := (voteStamp_entry_clock M F R E) hv
  rw [hτ] at hst
  have hτeq : τ = (((x.st (k + 1) u).t : Int) : Stamp) := Option.some.inj hst
  rw [hτeq, (clock_eq_clockValue M F) x R (k + 1) u] at hlt
  have hlt' : x.clockValue (k + 1) u < t := by
    have h := WithBot.coe_lt_coe.1 hlt
    exact_mod_cast h
  have huk : u ∉ A.corrupted (k + 1) := fun h => huK (E.corrupted_mono _ _ hk h)
  exact ⟨k + 1, (le_tick_of_clockValue_lt M F) E hm huk hlt', hk1⟩

/-- **Kit fact, a block stamped before a tick's value was held by that tick.** When `u` ticks to the
clock value `t` at step `m`, is outside the adversary set after `K` steps, and its tree after `K`
steps holds `H` stamped before `t`, then its tree held `H` after some step `j ≤ m`.

Why: the genesis block is in every tree (`genesis_mem_T_of_exec`); another block entered the tree
after some step `k + 1 ≤ K` and is stamped with `u`'s clock value there (`blockStamp_entry_clock`,
`clock_eq_clockValue`), less than `t`, so `k + 1 ≤ m` (`le_tick_of_clockValue_lt`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `K`: the step read; `m`: the
  tick's step; `u`: the validator; `t`: the tick's value; `H`: the block; `τ`: its stamp.

Read aloud: a block an honest validator stamped before `t` was in its tree by its tick to `t`. -/
theorem block_held_by_tick_of_stamp_lt {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {K m : ℕ} {u : V} {t : ℕ} {H : Block V} {τ : Stamp}
    -- step `m` is `u`'s tick to `t`
    (hm : x.lbl m = Event.tick u t)
    -- `u` is outside the adversary set after `K` steps
    (huK : u ∉ A.corrupted K)
    -- `u`'s tree after `K` steps holds `H`, stamped `τ`, before `t`
    (hH : H ∈ (x.st K u).tree) (hτ : (x.st K u).blockStamp H = some τ)
    (hlt : τ < (((t : ℕ) : Int) : Stamp)) :
    ∃ j ≤ m, H ∈ (x.st j u).tree := by
  by_cases hg : H = Block.genesis
  · exact ⟨m, le_rfl, hg ▸ (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E m u⟩
  obtain ⟨k, hk, -, hk1, hst⟩ := (blockStamp_entry_clock M F R E) hH hg
  rw [hτ] at hst
  have hτeq : τ = (((x.st (k + 1) u).t : Int) : Stamp) := Option.some.inj hst
  rw [hτeq, (clock_eq_clockValue M F) x R (k + 1) u] at hlt
  have hlt' : x.clockValue (k + 1) u < t := by
    have h := WithBot.coe_lt_coe.1 hlt
    exact_mod_cast h
  have huk : u ∉ A.corrupted (k + 1) := fun h => huK (E.corrupted_mono _ _ hk h)
  exact ⟨k + 1, (le_tick_of_clockValue_lt M F) E hm huk hlt', hk1⟩

/-- **Kit fact K2 for a node state the update leaves, with the supporter's vote.** As
`fast_block_has_honest_supporter_of_update`, and the supporter's tick `k` to the vote time of slot `s''` put on
the wire its vote for `H_v`: the vote the proof counts is the one `v`'s tick sent (`tick_vote_held_block`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- as `fast_block_has_honest_supporter`'s; `n₀`: the node state the update leaves.

Read aloud: a block fast in an honest updater's update of slot `s''` is an ancestor of, or is, a block some
honest active committee member of `s''` held at its tick to the vote time of `s''` and voted for there. -/
theorem fast_block_has_honest_supporter_vote_of_update (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (anchor s'' : ℕ) (u' : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hOwner : VotesCastByOwner M A x)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s'' + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s'' + 1))) (hAnchor : anchor ≤ M.slotStart S.C (s'' + 1))
    (hu' : u' ∈ updaterAt M S A x s'') (n₀ : M.N)
    (hCU₀ : GoldilocksCorrectness.Record.Statements.Routines.ConfirmationUpdated M S.C S.P (x.tickInput u' (M.supportCutoff S.C (s'' + 1)))
      ((M.supportCutoff S.C (s'' + 1) : ℕ) : Int) (s'' + 1) n₀) :
    ∀ D ∈ M.fastBlocks n₀,
      ∃ v ∈ honestActiveAt M S A x s'' ∩ S.P.committee s'',
        ∃ H_v ∈ (x.tickInput v (M.voteTime S.C s'')).tree, D.AncestorEq H_v ∧
          ∃ k : ℕ, x.lbl k = Event.tick v (M.voteTime S.C s'') ∧
            (⟨v, NamedObject.gfVote (GoldfishVote.mk v s'' H_v.root)⟩ : SignedMsg V (NamedObject V)) ∈
              x.sent (k + 1) - x.sent k := by
  intro D hD
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hT0 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S s''
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s'' + 1)
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s''
  -- `u'`'s tick `K` to the support cutoff `c` of slot `s'' + 1`, honest there
  have hu'w : u' ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s'' + 1))
      (M.supportCutoff S.C (s'' + 1)) := hu'
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hu'w
  have huK : u' ∉ A.corrupted K := E.not_mem_corrupted_of_tick hlK
  have hTI : x.tickInput u' (M.supportCutoff S.C (s'' + 1)) = x.st K u' := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlK]
  -- the duty window's start, read as an integer, is at most the model's natural-number start
  have hdwz : (Goldilocks.duty_window_start S.C (s'' + 1) : ℤ) ≤
      ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℤ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
    exact Int.self_le_toNat _
  have hdwr : ((Goldilocks.duty_window_start S.C (s'' + 1) : ℤ) : ℝ) ≤
      ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℝ) := by exact_mod_cast hdwz
  have hcc : (M.supportCutoff S.C s'' : ℝ) + Δ S ≤ M.supportCutoff S.C (s'' + 1) := by
    exact_mod_cast (show M.supportCutoff S.C s'' + Δ S ≤ M.supportCutoff S.C (s'' + 1) by omega)
  -- `u'` ticks, inside its window, to the support cutoff of slot `s''` at a step `m'` (under `hSkew`)
  have hc1 : 1 ≤ M.supportCutoff S.C s'' := by omega
  have hin := (mem_activeThroughoutToTick_of_inside M F) R E hu'w hc1
    (by
      have h1 : ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℝ) + 2 * Δ S ≤ M.supportCutoff S.C s'' := by
        exact_mod_cast (show M.dutyWindowStart S.C (s'' + 1) + 2 * Δ S ≤ M.supportCutoff S.C s'' by omega)
      have h2 : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      linarith)
    (by linarith)
  obtain ⟨m', hlm', -⟩ := Activity.mem_activeThroughoutToTick.1 hin
  -- every step up to `m'` is at a time before `c`
  have hm'c : ∀ i ≤ m', x.time i < (M.supportCutoff S.C (s'' + 1) : ℝ) := by
    intro i hi
    have h1 := (E.tick_active m' u' _ hlm').2.2
    have h2 := (time_mono M) x R hi
    linarith
  -- the early stamps' bound is the support cutoff of slot `s''`
  have hbound : (((S.C.t_ s'' + 2 * S.C.Δ : Time)) : Stamp) =
      ((((M.supportCutoff S.C s'' : ℕ) : Int)) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S s'']
  -- the update `u'`'s tick ran (`hCU₀`), and the fast test `D` passed
  have hCU := hCU₀
  obtain ⟨-, -, -, -, -, -, hfast⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_fast_cases (Nat.le_add_left 1 s'')
      hCU hD
  simp only [Nat.add_sub_cancel] at hfast
  rw [hTI] at hfast
  set sv := SupportVotes M S.C (x.st K u') s'' with hsv_def
  have hRΦ : RootsNameBlocksIn (M.fg_to_ac (x.st K u')).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x R E K u'
  rw [fast_test_eq_ok_true_iff _ hRΦ] at hfast
  -- the votes counted are early votes of `u'`'s pool of slot `s''`
  have hsv : sv ⊆ M.votesHeldSet (x.st K u') s'' := by
    intro vote hvote
    simp only [hsv_def, SupportVotes, EarlyVotes, Finset.mem_filter] at hvote
    exact hvote.1.1
  have hearly : ∀ vote ∈ sv, ∃ y : Stamp, GoldilocksCorrectness.Record.Statements.Routines.ResolvesAt M (x.st K u') vote y ∧
      y < ((((M.supportCutoff S.C s'' : ℕ) : Int)) : Stamp) := by
    intro vote hvote
    simp only [hsv_def, SupportVotes, EarlyVotes, Finset.mem_filter] at hvote
    obtain ⟨y, hy, hylt⟩ := hvote.1.2
    exact ⟨y, hy, hbound ▸ hylt⟩
  -- a counted vote of a validator honest at `c` was put on the wire by that validator's own tick
  have hsend : ∀ vote ∈ sv, ∀ v : V, vote.val_index = v →
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s'' + 1)) →
      ∃ k t' : ℕ, x.lbl k = Event.tick v t' ∧
        (⟨v, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k := by
    intro vote hvote v hval hvc
    obtain ⟨y, ⟨τv, τH, H', hτv, -, -, -, -, rfl⟩, hy⟩ := hearly vote hvote
    obtain ⟨j, hj, hvj⟩ := (vote_held_by_tick_of_stamp_lt M F) R E hlm' huK (hsv hvote) hτv
      (lt_of_le_of_lt (le_max_left _ _) hy)
    obtain ⟨i, hi, sm, hsm, hcarry⟩ := (pool_vote_sent M F) x R E hvj
    have hti : x.time i ≤ (M.supportCutoff S.C (s'' + 1) : ℝ) :=
      (hm'c i (by omega)).le
    have hhon : vote.val_index ∉ A.corrupted i := hval ▸ Activity.not_mem_corruptedAtTime.1 hvc i hti
    obtain ⟨k, t', -, hlk, hsk⟩ := hOwner i sm vote hsm hcarry hhon
    subst hval
    exact ⟨k, t', hlk, hsk⟩
  have hdisj : Disjoint (GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac (x.st K u')) sv sv s'' D)
      (equivocators sv) :=
    GoldilocksCorrectness.Proofs.Routines.disjoint_supportersOf_equivocators
  have hcard := Finset.card_union_of_disjoint hdisj.symm
  have hlt := hSleepK (s'' + 1) (by omega) hAnchor le_rfl
  simp only [Nat.add_sub_cancel] at hlt
  have hcomm : ∀ vote ∈ sv, vote.val_index ∈ S.P.committee s'' := fun vote hvote =>
    (GoldilocksCorrectness.Record.Statements.Executions.pool_committee_of_exec M F) S A x R E K u' s'' vote
      (hsv hvote)
  -- a member of `honestActiveAt M S A x s''` is honest at the cutoff
  have hHA : ∀ v ∈ honestActiveAt M S A x s'',
      v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s'' + 1)) := fun v hv h =>
    (Finset.mem_sdiff.1 hv).2 (Finset.mem_union_left _ h)
  -- `m'` comes before `K`: `u'`'s clock reads the support cutoff of slot `s''` after `m' + 1` steps
  have hm'K : m' < K := by
    by_contra hKm
    have hcs : M.supportCutoff S.C s'' + Δ S ≤ M.supportCutoff S.C (s'' + 1) := by omega
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hKm) with h | h
    · have h1 := E.clock_mono K m' u' _ _ h (E.not_mem_corrupted_of_tick hlm') (Or.inl hlK) (Or.inl hlm')
      omega
    · subst h
      rw [hlK] at hlm'
      have := (Event.tick.inj hlm').2
      omega
  by_contra hno
  have hsub : equivocators sv ∪
      GoldilocksCorrectness.Proofs.Routines.supportersOf (M.fg_to_ac (x.st K u')) sv sv s'' D ⊆
      S.P.committee s'' \ honestActiveAt M S A x s'' := by
    intro v hv
    rcases Finset.mem_union.1 hv with hEq | hS
    · -- an equivocator: two distinct votes of `v` counted, so `v` is not honest at `c`
      rw [GoldilocksCorrectness.Proofs.Routines.mem_equivocators_iff] at hEq
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega :
        1 < (votes_by sv v).card)
      obtain ⟨ha1, ha2⟩ := (GoldilocksCorrectness.Proofs.Routines.mem_votes_by_iff _ _ _).1 ha
      obtain ⟨hb1, hb2⟩ := (GoldilocksCorrectness.Proofs.Routines.mem_votes_by_iff _ _ _).1 hb
      refine Finset.mem_sdiff.2 ⟨ha2 ▸ hcomm a ha1, fun hvG => hab ?_⟩
      obtain ⟨k₁, t₁, hl₁, hs₁⟩ := hsend a ha1 v ha2 (hHA v hvG)
      obtain ⟨k₂, t₂, hl₂, hs₂⟩ := hsend b hb1 v hb2 (hHA v hvG)
      refine (honest_vote_sent_once M F R E) hl₁ hl₂ hs₁ hs₂ ?_
      rw [(GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E K u' s'' a (hsv ha1),
        (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E K u' s'' b (hsv hb1)]
    · -- a supporter of `D` in `honestActiveAt M S A x s''` would be the witness
      obtain ⟨vote, hvote, hval, -, -, H, hH, hHr, hDH⟩ :=
        (GoldilocksCorrectness.Proofs.Routines.mem_supportersOf_iff _ _ _ _ _ _).1 hS
      have hvK : v ∈ S.P.committee s'' := hval ▸ hcomm vote hvote
      refine Finset.mem_sdiff.2 ⟨hvK, fun hvG => hno ?_⟩
      obtain ⟨k, t', hlk, hsk⟩ := hsend vote hvote v hval (hHA v hvG)
      have hslot := (GoldilocksCorrectness.Record.Statements.Executions.pool_slot_of_exec M F) S A x R E K u' s'' vote
        (hsv hvote)
      obtain ⟨hkt, H_v, hHvT, hveq⟩ := (tick_vote_held_block M F U) S A x R E hlk hsk hslot
      subst hkt
      -- the head block resolved before the cutoff of slot `s''`: `u'` held it by its tick `m'`
      obtain ⟨y, ⟨τv, τH, H', -, hH', hH'r, -, hτH, rfl⟩, hy⟩ := hearly vote hvote
      have hHH' : H = H' := hRΦ H hH H' hH' (hHr.trans hH'r.symm)
      subst hHH'
      obtain ⟨jH, hjH, hHj⟩ := (block_held_by_tick_of_stamp_lt M F) R E hlm' huK
        (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hH).1 hτH
        (lt_of_le_of_lt (le_max_right _ _) hy)
      -- `v`'s vote-time tick `k` is at a time before `c`
      have hkc : x.time k ≤ (M.supportCutoff S.C (s'' + 1) : ℝ) := by
        have h1 := (E.tick_active k v _ hlk).2.2
        have h3 : (M.voteTime S.C s'' : ℝ) + Δ S ≤ M.supportCutoff S.C (s'' + 1) := by
          exact_mod_cast (show M.voteTime S.C s'' + Δ S ≤ M.supportCutoff S.C (s'' + 1) by omega)
        linarith
      have hTIv : x.tickInput v (M.voteTime S.C s'') = x.st k v := by
        unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlk]
      have hHvk : H_v ∈ (x.st k v).tree := hTIv ▸ hHvT
      have hHH : H = H_v :=
        hRoots H H_v ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := jH) (v := u') (fun h => huK (E.corrupted_mono _ _ (by omega) h)) ((hm'c jH hjH).le) hHj)
          ((GoldilocksCorrectness.Record.Proofs.Executions.inHonestTreeBy_of_st M F) x R E (i := k) (v := v) (Activity.not_mem_corruptedAtTime.1 (hHA v hvG) k hkc) hkc hHvk) (by rw [hHr, hveq])
      rw [hHH] at hDH
      exact ⟨v, Finset.mem_inter.2 ⟨hvG, hvK⟩, H_v, hHvT, hDH, k, hlk, hveq ▸ hsk⟩
  refine GoldilocksCorrectness.Proofs.Executions.fast_test_fails_of_minority _ _ _ hsub hlt ?_
  rw [hcard]
  exact hfast

/-- **Kit fact K2 for a node state the update leaves.** `fast_block_has_honest_supporter` for a fast block
of a node state `n₀` the record's confirmation update of slot `s'' + 1` leaves from the updater's tick input
(`ConfirmationUpdated`), rather than of the tick's output: the proof is that theorem's, with the update read from
`hCU₀`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- as `fast_block_has_honest_supporter`'s; `n₀`: the node state the update leaves.

Read aloud: a block fast in an honest updater's update of slot `s''` is an ancestor of, or is, a block some
honest active committee member of `s''` held at the vote time of `s''`. -/
theorem fast_block_has_honest_supporter_of_update (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (anchor s'' : ℕ) (u' : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hOwner : VotesCastByOwner M A x)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s'' + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s'' + 1))) (hAnchor : anchor ≤ M.slotStart S.C (s'' + 1))
    (hu' : u' ∈ updaterAt M S A x s'') (n₀ : M.N)
    (hCU₀ : GoldilocksCorrectness.Record.Statements.Routines.ConfirmationUpdated M S.C S.P (x.tickInput u' (M.supportCutoff S.C (s'' + 1)))
      ((M.supportCutoff S.C (s'' + 1) : ℕ) : Int) (s'' + 1) n₀) :
    ∀ D ∈ M.fastBlocks n₀,
      ∃ v ∈ honestActiveAt M S A x s'' ∩ S.P.committee s'',
        ∃ H_v ∈ (x.tickInput v (M.voteTime S.C s'')).tree, D.AncestorEq H_v := by
  intro D hD
  obtain ⟨v, hv, H_v, hHv, hDH, -⟩ := (fast_block_has_honest_supporter_vote_of_update M F U) S A x R anchor s'' u' E
    hSkew hOwner hRoots hSleepK hAnchor hu' n₀ hCU₀ D hD
  exact ⟨v, hv, H_v, hHv, hDH⟩

/-- **Kit fact K2: a fast block has an honest active supporter who held it.** The proof; the
audited statement is in `Statements/Executions/PeriodFastSupportStatements.lean`. The proof of
`fast_blocks_compatible_of_votes_updater` up to the fast test, which `D` passed: the committee of
`s''` is at most twice `D`'s score, the equivocators and the supporters of `D` among the votes
counted. If none of them were in `honestActiveAt M S Sched s''`, they would all be committee members
outside it, which `CommitteeSleepiness` makes fewer than half of the committee
(`fast_test_fails_of_minority`). An equivocator in it is impossible (one vote per honest owner,
`unique_vote_of_owner`); so a supporter `v` in it has a counted vote whose head names a block of
`u'`'s frame tree that is `D` or a descendant of `D`, and that vote is the one `v`'s tick sent at
the vote time of `s''`, for a block `H_v` it held (`tick_vote_held_block`); the two blocks have one
root, so are one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s''`: the slot of the votes; `u'`: the updater.

Read aloud: a block an honest updater fast-confirmed at the update of slot `s''` is an ancestor of,
or is, a block some honest active committee member of `s''` held at the vote time of `s''`. -/
theorem fast_block_has_honest_supporter (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (anchor s'' : ℕ) (u' : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hOwner : VotesCastByOwner M A x)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s'' + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s'' + 1))) (hAnchor : anchor ≤ M.slotStart S.C (s'' + 1))
    (hu' : u' ∈ updaterAt M S A x s'') :
    ∀ D ∈ (x.tickOutput u' (M.supportCutoff S.C (s'' + 1))).fastBlocks,
      ∃ v ∈ honestActiveAt M S A x s'' ∩ S.P.committee s'',
        ∃ H_v ∈ (x.tickInput v (M.voteTime S.C s'')).tree, D.AncestorEq H_v := by
  intro D hD
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hT0 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S s''
  have hT1 := (GoldilocksCorrectness.Record.Proofs.Routines.times_le M.toSlotLayout F.sched) S (s'' + 1)
  have hdw := (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_succ_le_slotStart M.toSlotLayout F.sched) S s''
  -- `u'`'s tick `K` to the support cutoff `c` of slot `s'' + 1`, honest there
  have hu'w : u' ∈ A.activeThroughoutToTick x (Goldilocks.duty_window_start S.C (s'' + 1))
      (M.supportCutoff S.C (s'' + 1)) := hu'
  obtain ⟨K, hlK, -⟩ := Activity.mem_activeThroughoutToTick.1 hu'w
  have huK : u' ∉ A.corrupted K := E.not_mem_corrupted_of_tick hlK
  have hTI : x.tickInput u' (M.supportCutoff S.C (s'' + 1)) = x.st K u' := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hlK]
  -- the duty window's start, read as an integer, is at most the model's natural-number start
  have hdwz : (Goldilocks.duty_window_start S.C (s'' + 1) : ℤ) ≤
      ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℤ) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_eq_toNat M.toSlotLayout F.sched U)]
    exact Int.self_le_toNat _
  have hdwr : ((Goldilocks.duty_window_start S.C (s'' + 1) : ℤ) : ℝ) ≤
      ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℝ) := by exact_mod_cast hdwz
  have hcc : (M.supportCutoff S.C s'' : ℝ) + Δ S ≤ M.supportCutoff S.C (s'' + 1) := by
    exact_mod_cast (show M.supportCutoff S.C s'' + Δ S ≤ M.supportCutoff S.C (s'' + 1) by omega)
  -- `u'` ticks, inside its window, to the support cutoff of slot `s''` at a step `m'` (under `hSkew`)
  have hc1 : 1 ≤ M.supportCutoff S.C s'' := by omega
  have hin := (mem_activeThroughoutToTick_of_inside M F) R E hu'w hc1
    (by
      have h1 : ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℝ) + 2 * Δ S ≤ M.supportCutoff S.C s'' := by
        exact_mod_cast (show M.dutyWindowStart S.C (s'' + 1) + 2 * Δ S ≤ M.supportCutoff S.C s'' by omega)
      have h2 : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      linarith)
    (by linarith)
  obtain ⟨m', hlm', -⟩ := Activity.mem_activeThroughoutToTick.1 hin
  -- every step up to `m'` is at a time before `c`
  have hm'c : ∀ i ≤ m', x.time i < (M.supportCutoff S.C (s'' + 1) : ℝ) := by
    intro i hi
    have h1 := (E.tick_active m' u' _ hlm').2.2
    have h2 := (time_mono M) x R hi
    linarith
  -- the early stamps' bound is the support cutoff of slot `s''`
  have hbound : (((S.C.t_ s'' + 2 * S.C.Δ : Time)) : Stamp) =
      ((((M.supportCutoff S.C s'' : ℕ) : Int)) : Stamp) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S s'']
  -- the update `u'`'s tick ran, and the fast test `D` passed
  obtain ⟨τ, hτ, hτle⟩ := (tickInput_awakeSince_of_mem_activeThroughoutToTick M F U) x R E hu'w
    (by
      have h := (dutyWindowStart_succ_lt_supportCutoff M F U) S s''
      have h' : ((M.dutyWindowStart S.C (s'' + 1) : ℕ) : ℤ) < ((M.supportCutoff S.C (s'' + 1) : ℕ) : ℤ) := by
        exact_mod_cast h
      exact lt_of_le_of_lt hdwz h')
  obtain ⟨n'', sent, hrun, hAwF, -, hfb, -, -⟩ :=
    (update_state_of_tick M F U) S A x R s'' u' E hlK ⟨τ, hτ, hτle⟩
  rw [hfb] at hD
  have hCU := (confirmationUpdated_of_cutoff_tickInput M F U) x R s'' u' n'' sent hrun hAwF
  exact (fast_block_has_honest_supporter_of_update M F U) S A x R anchor s'' u' E hSkew hOwner hRoots
    hSleepK hAnchor hu' n'' hCU D hD

end GoldilocksCorrectness.Record.Proofs.Executions

