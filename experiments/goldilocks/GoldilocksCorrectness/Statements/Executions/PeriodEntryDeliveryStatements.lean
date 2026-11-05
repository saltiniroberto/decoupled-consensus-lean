module
public import GoldilocksCorrectness.Proofs.Executions.PeriodEntryDelivery

@[expose] public section

/-! kit statements, new, no landed statement changes. Proved in
`GoldilocksCorrectness/Proofs/Executions/PeriodEntryDelivery.lean`.

- `fast_blocks_ancestorEq_saved_of_updater`: the fast blocks an updater of slot `s'` holds right
  after its update are ancestors of, or are, the confirmation it saved for `s'`;
- `cert_entry_held_before_freeze`: at a slot whose previous votes were not owed inside the period,
  a certified block of a chain an honest active voter holds before its vote, of chain-state height
  greater than `B`'s and compatible with the voter's finalized block, was in the voter's tree
  before its view froze.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff viewFreeze)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The fast blocks of an update are ancestors of its saved confirmation.** In an execution
that reaches every time, with permanent corruption: for an updater `u` of slot `s'`, when the
state right after its tick at `supportCutoff S (s' + 1)` has saved `C'` as the confirmation of slot
`s'`, every fast block of that state is `C'` or an ancestor of `C'`.

Why: the tick ran the confirmation update of slot `s' + 1`, whose answer's saved confirmation and
fast blocks are the state's; the update's fast blocks are blocks of its path, the ancestors of the
confirmation it saves (`fast_blocks_ancestorEq_saved`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the updater;
  `C'`: the saved confirmation.

Read aloud: an updater's fast blocks of slot `s'` are on the chain of the confirmation it saved
for `s'`. -/
theorem fast_blocks_ancestorEq_saved_of_updater (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (u : V) (C' : Block V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- a validator in the adversary set stays in it
    (hMono : Sched.MonotoneCorruption)
    -- `u` is awake and honest through the update of slot `s'`
    (hu : u ∈ updaterAt S Sched s')
    -- the update saved `C'` as the confirmation of slot `s'`
    (hSaved : (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.saved_confirmation s' = some C') :
    ∀ D ∈ (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.fast_blocks, D.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Executions.fast_blocks_ancestorEq_saved_of_updater S Sched x s' u
    C' hDiv hMono hu hSaved

/-- **Kit fact K3: the certified entry reaches the voter before its view freezes.** Under the
hypotheses `P` of the period after the hand-over slot `s` (with `GST` at or before the vote time
of slot `s + 1`), and with roots naming blocks among what honest validators hold up to the vote
time of slot `s'`, `s + 2 ≤ s'`: take a slot `s'` whose previous slot's votes were not owed inside
the period, a validator `u ∈ honestActiveAt S Sched s'`, a block `Y` that `u` holds before its tick
at the vote time of `s'`, and a progress certificate on the chain of `Y` at the height `h` naming
the block `T`, `T` an ancestor of `Y` or `Y`. When `T`'s chain-state height is greater than `B`'s
and `u`'s finalized block before the view freeze of slot `s' − 1` is compatible with `T`, then `u`
held `T` before that view freeze.

Why: the certificate's honest attester `uₐ` held `T` before its tick at
`supportCutoff S (sₐ + 1)`, with `sₐ + 1 ≤ s' − 1` (K1, `cert_entry_held_by_attester`). When the
previous votes were due after the period, `T` reaches `u` one delay after
`supportCutoff S (s' − 1)`, the view freeze. When they were due before it, `T` reaches `u` one
delay after `voteTime S (s' − 1)`, from the attester when `sₐ + 1 < s' − 1`, and otherwise from an
honest active supporter at slot `sₐ` of the fast block `T` descends from (K2,
`fast_block_has_honest_supporter`); the case `sₐ = s` is empty, the hand-over update's fast blocks
being ancestors of `B`, of height at most `B`'s.

 every
hypothesis is read.

The variables:
- `P`: the hypotheses of the period; `s'`: the slot of the vote; `u`: the voter; `Y`: the held
  block; `T`: the certified block; `h`: its height.

Read aloud: at a slot whose previous votes were not owed inside the period, a certified block of a
chain an honest active voter holds before its vote, of chain-state height greater than `B`'s and
compatible with the voter's finalized block, was in the voter's tree before its view froze. -/
theorem cert_entry_held_before_freeze {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (u : V)
    (Y T : Block V) (h : Height)
    -- roots name blocks among what honest validators hold up to the vote time of `s'`
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    -- the slot is at least two after the hand-over slot
    (hs' : s + 2 ≤ s')
    -- the votes of slot `s' − 1` were not owed inside the period
    (hgood : ¬ VotesOwedInPeriod S b₀ b₁ s')
    -- `u` is awake through the duties of `s'` and honest at its update
    (hu : u ∈ honestActiveAt S Sched s')
    -- `u` holds `Y` before its tick at the vote time of `s'`
    (hY : Y ∈ (stateBefore x (voteTime S s') u).S.T)
    -- `T` is an ancestor of `Y`, or `Y`
    (hTY : T.AncestorEq Y)
    -- the chain of `Y` carries a progress certificate at `h` naming `T`
    (hJ : ProgressCertOn Y h T)
    -- `T` is higher than `B`
    (hTB : (chainStateOf S.C B).h < (chainStateOf S.C T).h)
    -- `u`'s finalized block before the view freeze of `s' − 1` is compatible with `T`
    (hF : (stateBefore x (viewFreeze S (s' - 1)) u).S.F.compatible T = true) :
    T ∈ (stateBefore x (viewFreeze S (s' - 1)) u).S.T :=
  GoldilocksCorrectness.Proofs.Executions.cert_entry_held_before_freeze P s' u Y T h hRoots hs'
    hgood hu hY hTY hJ hTB hF

end GoldilocksCorrectness.Statements.Executions
