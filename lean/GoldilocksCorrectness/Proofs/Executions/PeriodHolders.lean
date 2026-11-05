module
public import GoldilocksCorrectness.Proofs.Routines.PeriodLocks
public import GoldilocksCorrectness.Statements.Executions.AsyncResilienceDefs
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.Relay
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# The lock holders inside the asynchronous period

The hypotheses every step lemma of the asynchronous period takes, bundled (`AsyncHyps`), and the
facts about a validator holding the lock on the hand-over block `B` inside the period:

- `exists_vote_of_mem_opponents`, `double_lt_of_sdiff`: the counting steps for the opponents of
  `B` at a revocation inside the period;
- what a step does to a validator's lock entries, record and fast blocks (`step_cases_period`,
  through `ac_on_tick_period_cases` and `tick_period_cases`), and two kit facts: every lock entry
  is on a held block (`lock_entry_mem_T_of_exec`) and none is on the genesis block
  (`lock_entry_ne_genesis_of_exec`).




-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_cast
  supportCutoff_eq voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section Period

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)

/-- unforgeability; fewer than a quorum ever corrupted (Lemma
87's conclusion); committee sleepiness from `anchor`, at or before the start of slot `s + 1`;
`GST` at or before `b₀`; the period's bounds; the lock holders' majority;
`t₀` at or before the hand-over cutoff; and the hand-over facts, whose last clause reads the
confirmed tips from `tAwakeEnd` on. -/
structure AsyncHyps (GST s : ℕ) (B : Block V) (H t₀ anchor tAwakeEnd b₀ b₁ : ℕ) : Prop where
  hDiv : TimeDiverges x.toTrace
  hMono : Sched.MonotoneCorruption
  hSync : SynchronyFromWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁
  hCatch : CatchUpOnWakeOutside Sched x.toTrace (Δ S) GST acObject b₀ b₁
  hSyncF : SynchronyFromWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁
  hCatchF : CatchUpOnWakeOutside Sched x.toTrace (Δ_F S) GST fgObject b₀ b₁
  hParent : ParentHeldAtDelivery S Sched x
  hOwner : VotesCastByOwner S Sched x
  hU : Unforgeability Vocab.goldilocks Sched x.toTrace
  hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t
  hSleepK : CommitteeSleepiness S Sched anchor
  hAnchor : anchor ≤ slotStart S (s + 1)
  hGST : GST ≤ b₀
  hb₀ : supportCutoff S (s + 1) ≤ b₀
  hb : b₀ ≤ b₁
  hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k)
  hHold : HoldersOutweighWhereOwed S Sched s b₀ b₁
  ht₀ : t₀ ≤ supportCutoff S (s + 1)
  hHand : HandoverFacts S Sched x s B H t₀ tAwakeEnd

end Period

end GoldilocksCorrectness.Statements.Executions

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A subset of `C \ G`, counted twice, is smaller than `C` when `C \ G` is smaller than
`G ∩ C`.

The variables:
- `opp`: the subset; `C`, `G`: the two sets. -/
theorem double_lt_of_sdiff {opp C G : Finset V} [DecidableEq V] (hsub : opp ⊆ C \ G)
    (hlt : |C \ G| < |G ∩ C|) : 2 * |opp| < |C| := by
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter C G
  rw [Finset.inter_comm] at hlt
  omega

/-! ## The step of the lock holder's invariant -/

/-- **Kit fact: every lock entry is on a held block.** At every step of every execution, the block
of every lock entry a validator holds is a block of its FG state's tree.

Why: the entry is traced (`lockTraced_of_mem`): its block is an ancestor of a block of the frame's
tree at an earlier step, or that block; the tree only grows (`mem_T_mono`) and holds every
ancestor of its blocks (`ancestors_mem_T_of_exec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `v`: the validator; `i`: the step.

Read aloud: a validator holds every block it has locked. -/
theorem lock_entry_mem_T_of_exec (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (v : V) (i : ℕ) :
    ∀ e ∈ (x[i][v].st).A.lock_entries, e.B ∈ (x[i][v].st).S.T := by
  intro e he
  obtain ⟨s, -, hlt, -, A', -, e₀, -, -, hT, -, -, -, hB, -⟩ := lockTraced_of_mem S Sched x v i e he
  have hT' := ((mem_fg_to_ac_tree _ _).1 hT).1
  unfold stateBefore at hT'
  exact ancestors_mem_T_of_exec S Sched x i v _ _ (mem_T_mono x v (le_of_lt hlt) hT') hB

section Steps

variable {S : Setup V} {Sched : Schedule V}

/-- What a step does to a validator's lock entries, record of the confirmed tip and fast blocks:
it keeps all three; or it is the tick of every awake validator at a time `t` at which the
validator is awake and honest, and the step leaves the lock entries of the validator's AC state
with its expired entries removed and keeps the other two fields, or (at the vote time of the slot
of `t`) leaves the lock entries of the revocation of that slot on that state and keeps the other
two fields, or (at the support cutoff of the slot of `t`) leaves the three fields of the
confirmation update of that slot on that state.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own tick changes its locks, record and fast blocks, and only
through the expiry, the revocation and the confirmation update. -/
theorem step_cases_period (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    ((x[i + 1][v].st).A.lock_entries = (x[i][v].st).A.lock_entries ∧
      (x[i + 1][v].st).A.latest_confirmed = (x[i][v].st).A.latest_confirmed ∧
      (x[i + 1][v].st).A.fast_blocks = (x[i][v].st).A.fast_blocks) ∨
    (∃ t : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      (((x[i + 1][v].st).A.lock_entries = (expireLocks (x[i][v].st).A t).lock_entries ∧
          (x[i + 1][v].st).A.latest_confirmed = (x[i][v].st).A.latest_confirmed ∧
          (x[i + 1][v].st).A.fast_blocks = (x[i][v].st).A.fast_blocks) ∨
        ((t : Int) = S.C.t_ (S.C.slot t) + S.C.Δ ∧ ∃ A' : ACState V,
          revoke_locks S.P (expireLocks (x[i][v].st).A t) (fg_to_ac (x[i][v].st).S) t
            (S.C.slot t) = .ok A' ∧
          (x[i + 1][v].st).A.lock_entries = A'.lock_entries ∧
          (x[i + 1][v].st).A.latest_confirmed = (x[i][v].st).A.latest_confirmed ∧
          (x[i + 1][v].st).A.fast_blocks = (x[i][v].st).A.fast_blocks) ∨
        ((t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ ∧ ∃ A'' : ACState V,
          update_confirmation S.C S.P (expireLocks (x[i][v].st).A t) (fg_to_ac (x[i][v].st).S)
            t (S.C.slot t) = .ok A'' ∧
          (x[i + 1][v].st).A.lock_entries = A''.lock_entries ∧
          (x[i + 1][v].st).A.latest_confirmed = A''.latest_confirmed ∧
          (x[i + 1][v].st).A.fast_blocks = A''.fast_blocks))) := by
  rcases step_cases x i v with h | ⟨t, n', sent, hl, hmem, hrun, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨hS, hA, -⟩ := tickInputState_frame x i t v
    rw [h]
    refine Or.inr ⟨t, hl, hmem, ?_⟩
    have hc := tick_period_cases S.C S.P S.X _ n' (t : Int) sent hrun
    rw [hA, hS] at hc
    exact hc
  · rw [h]
    obtain ⟨h1, -, h3, h4⟩ := receive_keeps_confirmation S.C S.P S.X (x[i][v].st) sm.msg
    rw [h1, h3, h4]
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- **Kit fact: no lock entry is on the genesis block.** At every step of every execution, no lock
entry a validator holds is on the genesis block.

Why: by induction on the step, through `step_cases_lock_saved`: the initial AC state holds no
entry; a step keeps a subset of the entries, or revokes (`revoke_locks_entry_ne_genesis`), or runs
the confirmation update, which adds only an entry on a block of its path
(`update_confirmation_in_frame`).

The variables:
- `x`: the execution; `v`: the validator; `i`: the step.

Read aloud: nobody locks the genesis block. -/
theorem lock_entry_ne_genesis_of_exec (x : AtomicExec (protocol S) Sched) (v : V) (i : ℕ) :
    ∀ e ∈ (x[i][v].st).A.lock_entries, e.B ≠ Block.genesis := by
  induction i with
  | zero =>
      intro e he
      rw [getElem_zero_st, initial_eq, acState_initial_eq] at he
      exact absurd he (Finset.notMem_empty e)
  | succ i ih =>
      intro e he
      rcases step_cases_lock_saved x i v with ⟨-, hsub⟩ | ⟨t, -, -, -, A', hA', -, hlk⟩ |
          ⟨t, -, -, -, -, A'', hA'', -, hlk⟩
      · exact ih e (hsub he)
      · rw [hlk] at he
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0, revoke_locks_zero] at hA'
          cases hA'
          exact ih e (Finset.mem_filter.1 he).1
        · exact revoke_locks_entry_ne_genesis (Nat.one_le_iff_ne_zero.mpr hs0) hA' e he
      · rw [hlk] at he
        rcases (update_confirmation_in_frame _ _ _ _ _ _ _ hA'').2.2.1 e he with h | ⟨-, h⟩
        · exact ih e (Finset.mem_filter.1 h).1
        · exact h

end Steps

end GoldilocksCorrectness.Proofs.Executions
