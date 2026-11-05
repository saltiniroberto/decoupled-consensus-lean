module
public import GoldilocksCorrectness.Proofs.Executions.PeriodFastSupport

@[expose] public section

/-! a kit statement, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/PeriodFastSupport.lean`.

- `fast_block_has_honest_supporter`: a block an honest updater fast-confirmed at the update of
  slot `s''` is an ancestor of, or is, the block some honest active committee member of `s''`
  voted for, which that member held at the vote time.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact K2: a fast block has an honest active supporter who held it.** In an execution
that reaches every time, with permanent corruption and no vote cast in an honest validator's
name, with roots naming blocks among what honest validators hold up to `supportCutoff S (s'' + 1)`
and committee sleepiness from `anchor`, at most the start of slot `s'' + 1`: for every fast block
`D` of the state right after the tick at `supportCutoff S (s'' + 1)` of an updater `u'` of slot
`s''`, some member `v` of the committee of `s''` in `honestActiveAt S Sched s''` held, before its
tick at the vote time of `s''`, a block `H_v` that is `D` or a descendant of `D`.

Why: `D` passed the fast test of the update of slot `s'' + 1`: the committee of `s''` is at most
twice `D`'s score, the equivocators and the supporters of `D` among the votes counted. Committee
sleepiness makes the committee members outside `honestActiveAt S Sched s''` fewer than half of the
committee, so some equivocator or supporter is in it (`fast_test_fails_of_minority`). It is no
equivocator (one vote per honest owner); as a supporter, its counted vote names, by its head, a
block of `u'`'s frame tree that is `D` or a descendant of `D`, and that vote is the one its tick
sent at the vote time of `s''`, for a block `H_v` it held then (Lemma 14); one root, one block.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s''`: the slot of the votes; `u'`: the updater.

Read aloud: a block an honest updater fast-confirmed at the update of slot `s''` is an ancestor of,
or is, a block some honest active committee member of `s''` held at the vote time of `s''`. -/
theorem fast_block_has_honest_supporter (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (anchor s'' : ℕ) (u' : V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- a validator in the adversary set stays in it
    (hMono : Sched.MonotoneCorruption)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    -- roots name blocks among what honest validators hold up to the cutoff of slot `s'' + 1`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' + 1)))
    -- committee sleepiness from `anchor`
    (hSleepK : CommitteeSleepiness S Sched anchor)
    -- `anchor` is at most the start of slot `s'' + 1`
    (hAnchor : anchor ≤ slotStart S (s'' + 1))
    -- `u'` is awake and honest through the update of slot `s''`
    (hu' : u' ∈ updaterAt S Sched s'') :
    ∀ D ∈ (stateBefore x (supportCutoff S (s'' + 1) + 1) u').A.fast_blocks,
      ∃ v ∈ honestActiveAt S Sched s'' ∩ S.P.committee s'',
        ∃ H_v ∈ (stateBefore x (voteTime S s'') v).S.T, D.AncestorEq H_v :=
  GoldilocksCorrectness.Proofs.Executions.fast_block_has_honest_supporter S Sched x anchor s'' u'
    hDiv hMono hOwner hRoots hSleepK hAnchor hu'

end GoldilocksCorrectness.Statements.Executions
